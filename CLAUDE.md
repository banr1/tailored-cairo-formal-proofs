# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Cairo言語の形式検証プロジェクト。Lean 4証明支援系を使用して、Cairo仮想マシンのセマンティクスとSTARKエンコーディングの正しさを検証する。

## Build Commands

```bash
# Mathlibのプリコンパイル済みファイルを取得（初回セットアップ時に必要）
lake exe cache get

# 全ファイルをコンパイル（検証を実行）
lake build
```

**注意**: `Verification/Libfuncs/u256/u256_guarantee_inv_mod_n_completeness.lean`はビルド時間とメモリ使用量の問題でコメントアウトされている。

## Development Environment

- **Lean Version**: v4.13.0-rc3
- **依存ライブラリ**: Mathlib4
- **推奨エディタ**: VS Code + Lean 4拡張機能

## Architecture

### Verification/Semantics/ - Cairo VMセマンティクス

- `Cpu.lean`: Cairo CPUの実行セマンティクス（健全性証明とSTARKエンコーディング検証用）
- `Vm.lean`: 抽象化されたVMセマンティクス（完全性証明用）
- `Instruction.lean`: 命令定義
- `Assembly.lean`: アセンブリレベルの仕様

**サブディレクトリ**:
- `Soundness/`: 健全性証明インフラ（Hoare論理ベース）
- `Completeness/`: 完全性証明インフラ
- `AirEncoding/`: STARK証明書生成用の代数的エンコーディング正当性証明

### Verification/Libfuncs/ - ライブラリ関数検証

各libfuncは以下のパターンに従う:
```
[libfunc_name]_code.lean                  # 実装コード
[libfunc_name]_soundness_spec.lean        # 健全性仕様
[libfunc_name]_soundness.lean             # 健全性証明
[libfunc_name]_completeness_spec.lean     # 完全性仕様
[libfunc_name]_completeness.lean          # 完全性証明
```

検証済みの整数型: u16, u32, u64, u128, u256, u512, bounded_int

### lean3/ - レガシーLean 3検証

CairoZero（旧Cairo 0）の検証コード。楕円曲線演算（secp256k1, secp256r1）とデジタル署名検証を含む。

## Key Concepts

- **Soundness（健全性）**: プログラムが仕様を満たすことの証明
- **Completeness（完全性）**: 仕様を満たす全ての実行がプログラムで表現可能であることの証明
- **AIR Encoding**: Algebraic Intermediate Representation - STARK証明に使用される実行トレースの代数的表現
