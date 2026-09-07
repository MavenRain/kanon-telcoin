import Lake
open Lake DSL

package «kanon-telcoin» where
  leanOptions := #[⟨`autoImplicit, false⟩]

lean_lib KanonMeta where
  srcDir := "third_party/kanon_meta"

@[default_target]
lean_lib KanonTelcoin

@[default_target]
lean_lib KanonTelcoinTests where
  roots := #[`test.NatFragmentBridge]
