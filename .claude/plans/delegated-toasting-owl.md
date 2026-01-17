# Cairo形式検証プロジェクト Lean 4教科書 - 実装計画

## 概要

`Verification/`ディレクトリのLean4実装を理解するための教科書をマークダウンファイルで生成する。

## 教科書の設計方針

### 対象読者

- Lean 4の基礎知識を持つプログラマ・研究者
- Cairo/STARKに興味がある形式検証の学習者

### 設計原則

1. **マクロ視点**: 全体アーキテクチャ、モジュール間の関係、各パートの役割
2. **ミクロ視点**: 1行1行の詳細解説、型の意味、証明の戦略
3. **前提知識の体系化**: 有限体、Hoare論理、STARK/AIRの基礎を搭載
4. **豊富な図解**: Mermaid図によるアーキテクチャ・データフロー・証明構造の可視化

---

## 章構成（21章 + 付録3章）

### 第I部: 基礎編（前提知識）

| 章  | タイトル           | 主な内容                                             |
| :-: | :----------------- | :--------------------------------------------------- |
|  1  | 数学的基礎         | 有限体F_p、PRIME定数、ビットベクトル、Option型       |
|  2  | Lean 4基礎         | 基本構文、Structure、タクティック、Mathlib           |
|  3  | Cairo VM概要       | Cairo言語、VMアーキテクチャ、メモリモデル、STARK概要 |
|  4  | プログラム検証基礎 | Hoare論理、健全性/完全性、AIR概念                    |

### 第II部: Semanticsモジュール詳解

| 章  | タイトル              | 対象ファイル       | 行数  |
| :-: | :-------------------- | :----------------- | :---: |
|  5  | 命令定義              | `Instruction.lean` | 150行 |
|  6  | CPU実行セマンティクス | `Cpu.lean`         | 119行 |
|  7  | VM抽象セマンティクス  | `Vm.lean`          | 274行 |
|  8  | アセンブリ言語        | `Assembly.lean`    | 634行 |

### 第III部: 健全性証明インフラ

| 章  | タイトル           | 対象ファイル                  |  行数  |
| :-: | :----------------- | :---------------------------- | :----: |
|  9  | 健全性基盤         | `Soundness/Prelude.lean`      | ~150行 |
| 10  | Hoare論理実装      | `Soundness/Hoare.lean`        | 773行  |
| 11  | アセンブリステップ | `Soundness/AssemblyStep.lean` | ~200行 |

### 第IV部: 完全性証明インフラ

| 章  | タイトル     | 対象ファイル                   |
| :-: | :----------- | :----------------------------- |
| 12  | 完全性基盤   | `Completeness/VmAssembly.lean` |
| 13  | VM Hoare論理 | `Completeness/VmHoare.lean`    |

### 第V部: AIR Encodingの正当性

| 章  | タイトル             | 対象ファイル                   |
| :-: | :------------------- | :----------------------------- |
| 14  | 制約システム         | `AirEncoding/Constraints.lean` |
| 15  | 命令エンコーディング | `AirEncoding/Instruction.lean` |
| 16  | 実行存在定理         | `AirEncoding/Correctness.lean` |

### 第VI部: Libfuncs検証

| 章  | タイトル                               | 対象ファイル                      |
| :-: | :------------------------------------- | :-------------------------------- |
| 17  | 共通定義                               | `Libfuncs/Common.lean`            |
| 18  | u128_overflowing_add（ケーススタディ） | u128/u128*overflowing_add*\*.lean |
| 19  | 他のlibfunc検証パターン                | u128, u256, bounded_int           |

### 第VII部: 実践と応用

| 章  | タイトル               |
| :-: | :--------------------- |
| 20  | 新規libfunc検証の手順  |
| 21  | トラブルシューティング |

### 付録

- A: タクティック一覧
- B: 主要定義・定理索引
- C: 参考文献

---

## 必要なMermaid図解（15個）

### アーキテクチャ図

1. **プロジェクト全体構造図** - Semantics/Libfuncs/AirEncodingの関係
2. **Semanticsモジュール依存関係図** - Instruction → Cpu → Vm → Assembly
3. **Libfuncs検証フロー図** - 5ファイルパターン（code/spec/proof）

### データフロー図

4. **命令実行フロー図** - RegisterState遷移（pc, ap, fp）
5. **Mrelセグメント構造図** - prog/exec/rc/val/errorの関係
6. **レンジチェックフロー図** - rcBound検証の流れ

### 証明構造図

7. **健全性証明構造図** - Ensures → EnsuresbRet → spec
8. **完全性証明構造図** - Returns → LocalAssignment → Assign
9. **AIR制約関係図** - InputDataAux → Constraints → Correctness
10. **execution_exists証明フロー図** - 主定理の証明構造

### 状態遷移図

11. **CPU状態遷移図** - NextState述語の動作
12. **Instruction構造図** - 15ビットフラグの意味と配置

### シーケンス図

13. **健全性証明シーケンス** - step_assert_eq等のタクティック適用順
14. **完全性証明シーケンス** - vm*step*\*タクティックの適用順
15. **アセンブリ命令実行シーケンス** - assertEq/jump/call/ret

---

## ファイル分割方針

### ディレクトリ構造

```
docs/textbook/
├── README.md                           # 目次と概要
├── part1-foundations/
│   ├── ch01-mathematical-foundations.md
│   ├── ch02-lean4-basics.md
│   ├── ch03-cairo-vm-overview.md
│   └── ch04-program-verification.md
├── part2-semantics/
│   ├── ch05-instruction.md
│   ├── ch06-cpu.md
│   ├── ch07-vm.md
│   └── ch08-assembly.md
├── part3-soundness/
│   ├── ch09-soundness-prelude.md
│   ├── ch10-hoare-logic.md
│   └── ch11-assembly-step.md
├── part4-completeness/
│   ├── ch12-completeness-basics.md
│   └── ch13-vm-hoare.md
├── part5-air-encoding/
│   ├── ch14-constraints.md
│   ├── ch15-instruction-encoding.md
│   └── ch16-correctness.md
├── part6-libfuncs/
│   ├── ch17-common-definitions.md
│   ├── ch18-u128-overflowing-add.md
│   └── ch19-other-libfuncs.md
├── part7-practice/
│   ├── ch20-new-libfunc-verification.md
│   └── ch21-troubleshooting.md
└── appendices/
    ├── appendix-a-tactics.md
    ├── appendix-b-index.md
    └── appendix-c-references.md
```

### 推定サイズ

| パート     | ファイル数 |  推定行数   | 推定サイズ |
| :--------- | :--------: | :---------: | :--------: |
| README     |     1      |     200     |    8KB     |
| Part 1     |     4      |    2,500    |   108KB    |
| Part 2     |     4      |    3,100    |   141KB    |
| Part 3     |     3      |    2,800    |   130KB    |
| Part 4     |     2      |    1,600    |    74KB    |
| Part 5     |     3      |    2,500    |   115KB    |
| Part 6     |     3      |    3,200    |   148KB    |
| Part 7     |     2      |    1,000    |    45KB    |
| Appendices |     3      |     900     |    42KB    |
| **合計**   |   **25**   | **~17,800** | **~810KB** |

---

## 実装の優先順位

### Phase 1: コア構造（必須・最優先）

1. `ch05-instruction.md` - Instruction構造体の詳細解説
2. `ch06-cpu.md` - RegisterState、NextState、命令実行
3. `ch07-vm.md` - Mrel型、VmRegisterState、Equiv述語

### Phase 2: 証明インフラ（必須）

4. `ch10-hoare-logic.md` - Ensures/Ensuresb、step\_\*タクティック
5. `ch09-soundness-prelude.md` - PRIME、PreludeHyps
6. `ch13-vm-hoare.md` - Returns、LocalAssignment

### Phase 3: 実践例（推奨）

7. `ch18-u128-overflowing-add.md` - 完全なケーススタディ
8. `ch17-common-definitions.md` - 共通定義

### Phase 4: 高度な内容（推奨）

9. `ch14-constraints.md` - AIR制約システム
10. `ch16-correctness.md` - execution_exists定理

### Phase 5: 前提知識と応用（オプション）

11. `ch01-04` - 数学・Lean・Cairo・検証の基礎
12. `ch19-21` - 他のlibfunc、応用、トラブルシューティング
13. 付録 - タクティック一覧、索引、参考文献

---

## 各章の詳細構造（例：ch06-cpu.md）

```markdown
# 第6章: CPU実行セマンティクス (Cpu.lean)

## 6.1 概要

- 本章の目的
- Cpu.leanの役割
- 前提知識

## 6.2 アーキテクチャ図

[Mermaid: CPU状態遷移図]

## 6.3 RegisterState構造体

### 6.3.1 定義（1行1行解説）

### 6.3.2 各フィールドの意味

### 6.3.3 使用例

## 6.4 命令実行関数

### 6.4.1 op0関数の詳細

### 6.4.2 op1関数の詳細（Option型の役割）

### 6.4.3 resAux/res関数

### 6.4.4 dst関数

## 6.5 状態遷移関数

### 6.5.1 nextPc（プログラムカウンタ更新）

### 6.5.2 nextAp（アロケーションポインタ更新）

### 6.5.3 nextFp（フレームポインタ更新）

### 6.5.4 Asserts（アサーション条件）

## 6.6 NextState述語

### 6.6.1 Instruction.NextState

### 6.6.2 グローバルNextState

### 6.6.3 存在量化の意味

## 6.7 まとめ

- 重要な概念の復習
- 次章との関連
```

---

## 修正するファイル

| ファイルパス                                                       | 操作                     |
| :----------------------------------------------------------------- | :----------------------- |
| `docs/textbook/`                                                   | 新規ディレクトリ作成     |
| `docs/textbook/README.md`                                          | 新規作成                 |
| `docs/textbook/part1-foundations/ch01-mathematical-foundations.md` | 新規作成                 |
| ...                                                                | （計25ファイル新規作成） |

---

## 検証方法

### 1. マークダウンの整合性

```bash
# Markdownlintでの検証
npx markdownlint docs/textbook/**/*.md
```

### 2. Mermaid図のレンダリング確認

- VS Codeの「Markdown Preview Mermaid Support」拡張で確認
- GitHub上でのレンダリング確認

### 3. コード参照の正確性

- 記載されているファイルパス・行番号が実際のコードと一致しているか確認
- `lake build`でコードがビルドできることを確認

### 4. 読者視点でのレビュー

- 目次から各章への導線が明確か
- 前提知識の説明が十分か
- 図解が直感的理解を助けているか
