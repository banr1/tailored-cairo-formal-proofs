# 第20章: 新規libfunc検証の手順

本章では、新しいlibfuncを検証する際の具体的な手順を解説する。既存の検証パターンを参考に、自分で検証を行う方法を習得することが目標である。

## 20.1 概要

新規libfunc検証は以下の5ステップで行う：

```mermaid
graph LR
    Step1["1. コード定義"]
    Step2["2. 健全性仕様"]
    Step3["3. 健全性証明"]
    Step4["4. 完全性仕様"]
    Step5["5. 完全性証明"]

    Step1 --> Step2
    Step2 --> Step3
    Step3 --> Step4
    Step4 --> Step5
```

---

## 20.2 準備作業

### 20.2.1 ファイル構成

新しいlibfunc `new_func` を検証する場合、以下のファイルを作成：

```
Verification/Libfuncs/[type]/
├── new_func_code.lean                  # 実装コード
├── new_func_soundness_spec.lean        # 健全性仕様
├── new_func_soundness.lean             # 健全性証明
├── new_func_completeness_spec.lean     # 完全性仕様（オプション）
└── new_func_completeness.lean          # 完全性証明（オプション）
```

### 20.2.2 必要なインポート

```lean
-- _code.lean
import Verification.Semantics.Assembly

-- _soundness_spec.lean
import Verification.Libfuncs.Common

-- _soundness.lean
import Verification.Libfuncs.[type].new_func_soundness_spec
import Verification.Libfuncs.[type].new_func_code
import Verification.Semantics.Soundness.Prelude

-- _completeness_spec.lean
import Verification.Semantics.Completeness.VmHoare
import Verification.Libfuncs.Common

-- _completeness.lean
import Verification.Libfuncs.[type].new_func_completeness_spec
import Verification.Libfuncs.[type].new_func_code
```

---

## 20.3 ステップ1: コード定義

### 20.3.1 アセンブリコードの記述

Cairo libfuncのアセンブリコードを`casm`マクロで定義：

```lean
-- new_func_code.lean
import Verification.Semantics.Assembly

open Casm in
def new_func_code : Code := casm![
  -- アセンブリ命令を記述
  [ap + 0] = [fp + -3] + [fp + -4], ap++;  -- 例: 加算
  jmp rel 3 if [ap + -1] != 0;             -- 例: 条件分岐
  ret;
]
```

### 20.3.2 コードの構造を理解する

コードを定義する前に：

1. Cairoコンパイラの出力を確認
2. 各命令の意味を理解
3. 分岐構造を把握

---

## 20.4 ステップ2: 健全性仕様

### 20.4.1 spec\_関数の定義

人間が読みやすい形式で仕様を定義：

```lean
-- new_func_soundness_spec.lean
namespace new_func_soundness

variable {F : Type} [Field F] [PreludeHyps F]

/-- 新規関数の仕様（人間向け）-/
def spec_new_func (input output : F) : Prop :=
  ∀ n_input : ℕ, is_u128_of input n_input →
  ∃ n_output : ℕ, is_u128_of output n_output ∧
    n_output = f(n_input)  -- fは期待される数学的関数
```

### 20.4.2 auto*spec*関数の定義

コードから自動導出される仕様：

```lean
/-- 自動生成仕様（コード構造に対応）-/
def auto_spec_new_func (input output : F) : Prop :=
  ∃ intermediate : F,
  intermediate = input + 1 ∧
  IsRangeChecked (rcBound F) intermediate ∧
  output = intermediate
```

### 20.4.3 sound\_定理の宣言

auto_specからspecへの含意を証明：

```lean
/-- 健全性定理 -/
theorem sound_new_func {input output : F}
    (h_auto : auto_spec_new_func input output) :
    spec_new_func input output := by
  sorry  -- ステップ3で証明
```

---

## 20.5 ステップ3: 健全性証明

### 20.5.1 証明の基本構造

```lean
-- new_func_soundness.lean
theorem auto_new_func :
    ∀ mem, ∀ σ : RegisterState F,
    Ensuresb bound mem σ (auto_spec_new_func input output) := by
  -- タクティックで証明
  intro mem σ
  step_assert_eq ...
  step_jump ...
  step_ret ...
```

### 20.5.2 主要なタクティック

| タクティック      | 用途             | 使用場面       |
| :---------------- | :--------------- | :------------- |
| `step_assert_eq`  | アサーション命令 | 等式制約       |
| `step_jump`       | ジャンプ命令     | 無条件ジャンプ |
| `step_jnz`        | 条件分岐         | if文           |
| `step_call`       | 関数呼び出し     | サブルーチン   |
| `step_ret`        | リターン         | 関数終了       |
| `step_advance_ap` | AP更新           | メモリ割り当て |

### 20.5.3 証明のテンプレート

```lean
theorem auto_new_func :
    ∀ mem, ∀ σ : RegisterState F,
    Ensuresb bound mem σ (auto_spec_new_func input output) := by
  intro mem σ

  -- 命令ごとにステップを進める
  step_assert_eq h_eq with [ap + 0] = [fp + -3] + [fp + -4]

  -- 分岐がある場合
  step_jnz h_nz
  · -- ケース1: 条件成立
    step_ret
    -- 事後条件を満たすことを証明
    use_only intermediate
    exact ⟨h_rc, h_eq⟩
  · -- ケース2: 条件不成立
    step_ret
    ...
```

---

## 20.6 ステップ4: 完全性仕様（オプション）

### 20.6.1 Returns述語の定義

完全性は「仕様を満たす出力が存在する」ことを保証：

```lean
-- new_func_completeness_spec.lean
namespace new_func_completeness

/-- 完全性仕様：仕様を満たす出力に対するReturns述語 -/
def spec_new_func_completeness
    (input : F) (n_input : ℕ) (h_input : is_u128_of input n_input)
    (output : F) : Prop :=
  ∃ n_output : ℕ, is_u128_of output n_output ∧
    n_output = f(n_input)
```

### 20.6.2 LocalAssignmentの構築

メモリ割り当てを構築：

```lean
/-- ローカル変数の割り当て -/
def new_func_assignment (input : F) (n_input : ℕ) : LocalAssignment F where
  exec := fun i =>
    match i with
    | 0 => input + 1
    | 1 => ...
    | _ => 0
```

---

## 20.7 ステップ5: 完全性証明（オプション）

### 20.7.1 証明の構造

```lean
-- new_func_completeness.lean
theorem new_func_complete :
    ∀ input n_input h_input,
    Returns mem σ (spec_new_func_completeness input n_input h_input) := by
  intro input n_input h_input

  -- LocalAssignmentを構築
  use new_func_assignment input n_input

  -- 各ステップでメモリ条件を満たすことを証明
  constructor
  · -- 初期条件
    ...
  constructor
  · -- ステップ条件
    vm_step_assert_eq
    vm_step_jump
    ...
  · -- 終了条件
    ...
```

---

## 20.8 実践例: u128_increment

### 20.8.1 仮想的な関数

u128値を1増やす関数を検証する例：

```lean
-- u128_increment_code.lean
open Casm in
def u128_increment_code : Code := casm![
  [ap + 0] = [fp + -3] + 1, ap++;        -- result = input + 1
  [ap + 0] = [ap + -1] + (u128Limit - 1), ap++;  -- オーバーフローチェック用
  ret;
]
```

### 20.8.2 健全性仕様

```lean
-- u128_increment_soundness_spec.lean
def spec_u128_increment (input output : F) : Prop :=
  ∀ n_input : ℕ, is_u128_of input n_input →
  n_input < u128Max →  -- オーバーフローしない条件
  is_u128_of output (n_input + 1)

def auto_spec_u128_increment (input output : F) : Prop :=
  ∃ result : F, result = input + 1 ∧
  ∃ check : F, check = result + (u128Limit - 1) ∧
  IsRangeChecked (rcBound F) check ∧
  output = result
```

### 20.8.3 健全性証明

```lean
-- u128_increment_soundness.lean
theorem sound_u128_increment {input output : F}
    (h_auto : auto_spec_u128_increment input output) :
    spec_u128_increment input output := by
  rcases h_auto with ⟨result, h_result, check, h_check, h_rc, h_output⟩
  intro n_input ⟨n_input_lt, input_eq⟩ h_no_overflow

  -- checkがレンジチェックを通過 → result < u128Limit
  rcases h_rc with ⟨n_check, n_check_lt, check_eq⟩

  -- n_input + 1 < u128Limit を証明
  have h_result_bound : n_input + 1 < u128Limit := by
    omega  -- または詳細な算術証明

  constructor
  · exact h_result_bound
  · rw [h_output, h_result, input_eq]
    simp [Nat.cast_add, Nat.cast_one]
```

---

## 20.9 チェックリスト

### 20.9.1 コード定義

- [ ] Cairoコンパイラ出力と一致
- [ ] 全命令が正しくエンコード
- [ ] 分岐先アドレスが正確

### 20.9.2 健全性仕様

- [ ] spec\_\*が数学的に正しい
- [ ] auto*spec*\*がコード構造と対応
- [ ] 型境界（is_uN_of）が適切

### 20.9.3 健全性証明

- [ ] 全コードパスをカバー
- [ ] レンジチェック条件を使用
- [ ] 数学的等式が成立

### 20.9.4 完全性（オプション）

- [ ] LocalAssignmentが適切
- [ ] 全出力値を生成可能
- [ ] メモリ条件を満たす

---

## 20.10 ベストプラクティス

### 20.10.1 段階的な証明

1. まず`sorry`で構造を確認
2. 簡単なケースから証明
3. 複雑なケースを後回しに

### 20.10.2 既存コードの参考

類似関数を参考にする：

```lean
-- 参考: u128_overflowing_add は加算の良い例
-- 参考: u64_sqrt は平方根の例
-- 参考: u256_safe_divmod は複雑な分岐の例
```

### 20.10.3 デバッグ手法

```lean
-- 型を確認
#check auto_spec_new_func

-- 目標を表示
example : goal := by
  show_term
  sorry

-- 中間状態を確認
example : goal := by
  step_assert_eq h with ...
  trace "{h}"  -- 仮定を表示
  sorry
```

---

## 20.11 まとめ

新規libfunc検証の手順：

| ステップ      | 成果物                     | 必須 |
| :------------ | :------------------------- | :--: |
| 1. コード定義 | `*_code.lean`              |  ✓   |
| 2. 健全性仕様 | `*_soundness_spec.lean`    |  ✓   |
| 3. 健全性証明 | `*_soundness.lean`         |  ✓   |
| 4. 完全性仕様 | `*_completeness_spec.lean` |  △   |
| 5. 完全性証明 | `*_completeness.lean`      |  △   |

---

## 演習問題

1. u128_decrementの検証を設計せよ（1を引く関数）。
   - アンダーフロー時の処理を含める

2. 既存のu128_sqrtを参考に、u32_sqrtの検証構造を説明せよ。

3. 完全性証明が健全性証明より難しい理由を説明せよ。

---

## 参考

- 既存の検証例: `Verification/Libfuncs/u128/u128_overflowing_add_*.lean`
- Casmマクロ: `Verification/Semantics/Assembly.lean`
- Hoareタクティック: `Verification/Semantics/Soundness/Hoare.lean`
