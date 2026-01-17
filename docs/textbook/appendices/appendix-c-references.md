# 付録C: 参考文献

本付録では、本プロジェクトを理解するために参照すべき文献・リソースを分野別に紹介します。

---

## C.1 Cairo言語とStarkWare

### 公式ドキュメント

1. **Cairo Language Documentation**
   - URL: https://docs.cairo-lang.org/
   - 内容: Cairo言語の公式リファレンス

2. **Cairo 1.0 Book (The Cairo Programming Language)**
   - URL: https://book.cairo-lang.org/
   - 内容: Cairo 1.0の包括的な解説書

3. **StarkWare Documentation**
   - URL: https://docs.starkware.co/
   - 内容: StarkWareプラットフォームの技術文書

4. **Cairo Whitepaper**
   - 著者: Lior Goldberg, Shahar Papini, Michael Riabzev
   - URL: https://eprint.iacr.org/2021/1063
   - 内容: Cairo言語とSTARK証明システムの理論的基盤

### 技術論文

5. **"Cairo – a Turing-complete STARK-friendly CPU architecture"** (2021)
   - 著者: Lior Goldberg, Shahar Papini, Michael Riabzev
   - 内容: Cairo VMアーキテクチャの設計思想

6. **StarkWare公式ブログ**
   - URL: https://medium.com/starkware
   - 内容: STARKとCairoの技術解説記事

---

## C.2 STARK証明システム

### 基礎論文

7. **"Scalable, transparent, and post-quantum secure computational integrity"** (2018)
   - 著者: Eli Ben-Sasson, Iddo Bentov, Yinon Horesh, Michael Riabzev
   - 会議: IACR Cryptology ePrint Archive
   - URL: https://eprint.iacr.org/2018/046
   - 内容: STARKの原論文

8. **"STARK Friendly Hash Challenge"**
   - 著者: Eli Ben-Sasson et al.
   - URL: https://starkware.co/hash-challenge/
   - 内容: STARK用ハッシュ関数の設計要件

### 解説資料

9. **"STARK 101"**
   - URL: https://starkware.co/stark-101/
   - 内容: STARKの入門チュートリアル

10. **"Anatomy of a STARK"**
    - 著者: Alan Szepieniec
    - URL: https://aszepieniec.github.io/stark-anatomy/
    - 内容: STARKの詳細な構造解説

---

## C.3 AIR（Algebraic Intermediate Representation）

11. **"Algebraic Intermediate Representation"**
    - 内容: 実行トレースの代数的表現
    - 参照: Cairo Whitepaper Section 4

12. **"DEEP-ALI: Efficient Verification of AIR with Low Degree Extension"**
    - 著者: Eli Ben-Sasson et al.
    - 内容: AIR検証の効率化手法

---

## C.4 Lean 4証明支援系

### 公式リソース

13. **Lean 4 Documentation**
    - URL: https://lean-lang.org/
    - 内容: Lean 4の公式サイトとドキュメント

14. **"Theorem Proving in Lean 4"**
    - URL: https://lean-lang.org/theorem_proving_in_lean4/
    - 内容: Lean 4での定理証明入門

15. **"Functional Programming in Lean"**
    - URL: https://lean-lang.org/functional_programming_in_lean/
    - 内容: Lean 4での関数型プログラミング

16. **Lean 4 Reference Manual**
    - URL: https://lean-lang.org/lean4/doc/
    - 内容: 言語仕様とAPIリファレンス

### Mathlib

17. **Mathlib4 Documentation**
    - URL: https://leanprover-community.github.io/mathlib4_docs/
    - 内容: 数学ライブラリのAPIドキュメント

18. **Mathlib4 GitHub Repository**
    - URL: https://github.com/leanprover-community/mathlib4
    - 内容: ソースコードと開発情報

19. **"Mathematics in Lean"**
    - URL: https://leanprover-community.github.io/mathematics_in_lean/
    - 内容: Mathlibを使った数学の形式化チュートリアル

---

## C.5 形式検証とプログラム検証

### Hoare論理

20. **"An Axiomatic Basis for Computer Programming"** (1969)
    - 著者: C. A. R. Hoare
    - 雑誌: Communications of the ACM
    - 内容: Hoare論理の原論文

21. **"Practical Foundations for Programming Languages"** (2016)
    - 著者: Robert Harper
    - 出版: Cambridge University Press
    - 内容: プログラミング言語の形式的基礎

### 健全性と完全性

22. **"Separation Logic: A Logic for Shared Mutable Data Structures"** (2002)
    - 著者: John C. Reynolds
    - 会議: LICS 2002
    - 内容: 分離論理の基礎

23. **"The Semantics of Predicate Logic as a Programming Language"** (1976)
    - 著者: M. H. van Emden, R. A. Kowalski
    - 雑誌: JACM
    - 内容: 述語論理のプログラミング言語としての解釈

---

## C.6 有限体とその算術

24. **"A Course in Number Theory and Cryptography"** (1994)
    - 著者: Neal Koblitz
    - 出版: Springer
    - 内容: 数論と暗号理論の基礎

25. **"Handbook of Elliptic and Hyperelliptic Curve Cryptography"** (2006)
    - 編者: Henri Cohen, Gerhard Frey
    - 出版: CRC Press
    - 内容: 楕円曲線暗号の包括的リファレンス

26. **"Introduction to Finite Fields and Their Applications"** (1994)
    - 著者: Rudolf Lidl, Harald Niederreiter
    - 出版: Cambridge University Press
    - 内容: 有限体の理論と応用

---

## C.7 関連するLean形式検証プロジェクト

27. **Verified Software Toolchain (VST)**
    - URL: https://vst.cs.princeton.edu/
    - 内容: C言語の形式検証フレームワーク

28. **CompCert**
    - URL: https://compcert.org/
    - 内容: 形式検証されたCコンパイラ

29. **seL4**
    - URL: https://sel4.systems/
    - 内容: 形式検証されたマイクロカーネル

30. **CertiKOS**
    - URL: http://flint.cs.yale.edu/certikos/
    - 内容: 形式検証されたOSカーネル

---

## C.8 オンラインリソース

### チュートリアルとガイド

31. **Lean Zulip Chat**
    - URL: https://leanprover.zulipchat.com/
    - 内容: Leanコミュニティのチャット

32. **Lean Community Blog**
    - URL: https://leanprover-community.github.io/blog/
    - 内容: Lean関連の技術記事

### ツールとユーティリティ

33. **Lake (Lean Build System)**
    - URL: https://github.com/leanprover/lake
    - 内容: Lean 4のビルドシステム

34. **Lean 4 VS Code Extension**
    - URL: https://marketplace.visualstudio.com/items?itemName=leanprover.lean4
    - 内容: VS Code用Lean 4拡張機能

---

## C.9 本プロジェクト関連

35. **本プロジェクトのGitHubリポジトリ**
    - URL: https://github.com/starkware-libs/formal-proofs
    - 内容: ソースコードと開発履歴

36. **StarkWare形式検証チームの発表資料**
    - 内容: プロジェクトの設計と実装に関するプレゼンテーション

---

## C.10 推奨学習順序

### 初学者向け

1. **Lean 4基礎**: 文献[14], [15]
2. **数学ライブラリ**: 文献[19]
3. **Cairo概要**: 文献[1], [2]
4. **本教科書**: 第1章〜第4章

### 健全性・完全性を学びたい人向け

1. **Hoare論理**: 文献[20]
2. **プログラム検証**: 文献[21]
3. **本教科書**: 第9章〜第13章

### STARK/AIRを学びたい人向け

1. **STARK基礎**: 文献[7], [9], [10]
2. **Cairo VM**: 文献[5]
3. **AIR**: 文献[11], 本教科書第14章〜第16章

### 実践的なlibfunc検証

1. **本教科書**: 第17章〜第21章
2. **ソースコード**: `Verification/Libfuncs/`

---

## C.11 用語集

| 用語 | 英語 | 説明 |
|:--|:--|:--|
| 有限体 | Finite Field | 有限個の元を持つ体 |
| 素数体 | Prime Field | 素数位数の有限体 F_p |
| STARK | Scalable Transparent ARgument of Knowledge | スケーラブルで透明な知識の引数 |
| AIR | Algebraic Intermediate Representation | 代数的中間表現 |
| 健全性 | Soundness | 証明が正しければ命題が真 |
| 完全性 | Completeness | 真の命題は証明可能 |
| Hoare論理 | Hoare Logic | プログラム正当性の論理体系 |
| 事前条件 | Precondition | プログラム実行前に成り立つ条件 |
| 事後条件 | Postcondition | プログラム実行後に成り立つ条件 |
| レンジチェック | Range Check | 値が特定範囲内にあることの検証 |
| libfunc | Library Function | Sierraのライブラリ関数 |
| Sierra | Safe Intermediate Representation | Cairoの中間言語 |
| CASM | Cairo Assembly | Cairoのアセンブリ言語 |

---

## C.12 更新履歴

| 日付 | 更新内容 |
|:--|:--|
| 2026-01-17 | 初版作成 |

---

## C.13 フィードバック

本付録の内容に関するフィードバックは、GitHubリポジトリのIssueを通じてお寄せください。
