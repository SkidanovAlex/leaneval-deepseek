import Mathlib
import Submission.Work.SSGRoute.TateDual.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TateDual

open Work.Tate

/-- Computation rule for the descended evaluation pairing on representatives: on
`Hm1π a` and `H0π ψ` the pairing `pairQ` is the evaluation `ψ a`.  This is
`pairQ_mk` after the (definitional) identification of the `Work.Tate` quotient models
`Hm1 G A = ↥(K p G A) ⧸ K0 p G A` and `H0 G (DualMod p A) = ↥(fixSub p G A) ⧸ V0 p G A`
with the submodule quotients used in `pairQ_mk`. -/
theorem pairQ_Hm1π_H0π (p : ℕ) (G : Type) [Group G] [Fintype G]
    (A : Type) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
      [SMulCommClass G (ZMod p) A]
    (a : (Work.Tate.norm G A).ker)
    (ψ : Work.Tate.fixedSubgroup G (Work.SSGRoute.DualMod p A)) :
    pairQ p G A (Work.Tate.Hm1π G A a) (Work.Tate.H0π G (Work.SSGRoute.DualMod p A) ψ)
      = (ψ : Work.SSGRoute.DualMod p A) a := by
  have h1 : (Work.Tate.Hm1π G A a : Work.Tate.Hm1 G A)
      = Submodule.Quotient.mk (p := K0 p G A) (show ↥(K p G A) from a) := rfl
  have h2 : (Work.Tate.H0π G (Work.SSGRoute.DualMod p A) ψ
        : Work.Tate.H0 G (Work.SSGRoute.DualMod p A))
      = Submodule.Quotient.mk (p := V0 p G A) (show ↥(fixSub p G A) from ψ) := rfl
  rw [h1, h2, pairQ_mk]

/-- **Naturality of the degree-`0` Tate pairing `pairQ` in the coefficient module.**

For a finite group `G`, `𝔽_p`-modules `A`, `B` with compatible `G`-action and a `G`-equivariant
`𝔽_p`-linear `u : A → B`, the evaluation pairing
`pairQ : Ĥ⁻¹(G, A) × Ĥ⁰(G, A^∨) → 𝔽_p`, `⟨a, φ⟩ = φ a` (`A^∨ = DualMod p A`) is natural:
`⟨u_* x, φ⟩ = ⟨x, (u^∨)_* φ⟩` for `x : Ĥ⁻¹(G,A)` and `φ : Ĥ⁰(G,B^∨)`.  On representatives
`x = Hm1π a`, `φ = H0π ψ` this is the tautology `ψ (u a) = (u^∨ ψ) a` (`pairQ_mk`), the only
content being that `Hm1Map`/`H0Map` are computed on representatives
(`Hm1Map_Hm1π`, `H0Map_H0π`). -/
theorem pairQ_natural (p : ℕ) (G : Type) [Group G] [Fintype G]
    (A : Type) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
      [SMulCommClass G (ZMod p) A]
    (B : Type) [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
      [SMulCommClass G (ZMod p) B]
    (u : A →ₗ[ZMod p] B) (hu : ∀ (g : G) (a : A), u (g • a) = g • u a)
    (hdu : ∀ (g : G) (ψ : Work.SSGRoute.DualMod p B), u.dualMap (g • ψ) = g • u.dualMap ψ)
    (x : Work.Tate.Hm1 G A) (φ : Work.Tate.H0 G (Work.SSGRoute.DualMod p B)) :
    Work.SSGRoute.TateDual.pairQ p G B (Work.Tate.Hm1Map G A B u.toAddMonoidHom hu x) φ
      = Work.SSGRoute.TateDual.pairQ p G A x
          (Work.Tate.H0Map G (Work.SSGRoute.DualMod p B) (Work.SSGRoute.DualMod p A)
            u.dualMap.toAddMonoidHom hdu φ) := by
  -- Reduce to representatives `x = Hm1π a`, `φ = H0π ψ`.
  obtain ⟨a, ha⟩ := Work.Tate.Hm1π_surjective x
  obtain ⟨ψ, hψ⟩ := Work.Tate.H0π_surjective φ
  rw [← ha, ← hψ]
  -- Compute `Hm1Map`/`H0Map` on representatives (`Hm1Map_Hm1π`, `H0Map_H0π`, both `rfl`),
  -- spelled out so that the rewrite sees the `toAddMonoidHom` form of `hu`/`hdu`.
  rw [show Work.Tate.Hm1Map G A B u.toAddMonoidHom hu (Work.Tate.Hm1π G A a)
        = Work.Tate.Hm1π G B (Work.Tate.mapKer G A B u.toAddMonoidHom hu a) from rfl,
      show Work.Tate.H0Map G (Work.SSGRoute.DualMod p B) (Work.SSGRoute.DualMod p A)
            u.dualMap.toAddMonoidHom hdu (Work.Tate.H0π G (Work.SSGRoute.DualMod p B) ψ)
        = Work.Tate.H0π G (Work.SSGRoute.DualMod p A)
            (Work.Tate.mapFixed G (Work.SSGRoute.DualMod p B) (Work.SSGRoute.DualMod p A)
              u.dualMap.toAddMonoidHom hdu ψ) from rfl]
  -- Evaluate the pairing on both sides (`pairQ_Hm1π_H0π`).
  rw [pairQ_Hm1π_H0π]
  rw [pairQ_Hm1π_H0π]
  -- Reduce the two sides to `ψ (u a)` via `mapKer_apply`/`mapFixed_apply`.
  have hk := congrArg (fun z : B => (ψ : Work.SSGRoute.DualMod p B) z)
    (Work.Tate.mapKer_apply u.toAddMonoidHom hu a)
  have hf := congrArg (fun z : Work.SSGRoute.DualMod p A => z a)
    (Work.Tate.mapFixed_apply (G := G) (A := Work.SSGRoute.DualMod p B)
      (B := Work.SSGRoute.DualMod p A) u.dualMap.toAddMonoidHom hdu ψ)
  rw [hk, hf]
  -- The remaining identity is the defining property of `dualMap`.
  exact (LinearMap.dualMap_apply u (ψ : Work.SSGRoute.DualMod p B) (a : A)).symm

end Work.SSGRoute.TateDual
