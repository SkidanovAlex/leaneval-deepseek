import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Submission.Work.Shrinking.TensorPower
import Submission.Work.Shrinking.exists_ne_zero_of_polyMap_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

open scoped TensorProduct

set_option linter.style.haveILetI false

universe u

section Shrinking

variable {p : ℕ} [Fact p.Prime] {G M N : Type*} [Group G]
  [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
  [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
  [Module.Finite (ZMod p) M] [Module.Finite (ZMod p) N]

/-- **The shrinking lemma** (Proposition 2 of Schmidt–Wingberg, with the dimension count
made explicit): for `r > t · s · dim_𝔽_p (M^{⊗s} ⊗ N)`, any `t` elements of
`(M^r)^{⊗s} ⊗ N` are killed by the `G`-equivariant surjection
`(φ_a^{⊗s}) ⊗ id_N : (M^r)^{⊗s} ⊗ N → M^{⊗s} ⊗ N` for some `a ≠ 0`. -/
theorem exists_foldMap_rTensor_tensorPower_eq_zero {s t r : ℕ} (hs : 1 ≤ s)
    (hM : Nontrivial M)
    (h : t * s * Module.finrank (ZMod p) ((⨂[ZMod p]^s M) ⊗[ZMod p] N) < r)
    (z : Fin t → (⨂[ZMod p]^s (Fin r → M)) ⊗[ZMod p] N) :
    ∃ a : Fin r → ZMod p, a ≠ 0 ∧ Function.Surjective (foldMap (M := M) a) ∧
      ∀ i : Fin t,
        ((PiTensorProduct.map (fun _ : Fin s => foldMap (M := M) a)).rTensor N) (z i) = 0 := by
  haveI := hM
  have hMf : Module.Finite (ZMod p) (⨂[ZMod p]^s M) :=
    moduleFinite_tensorPower (p := p) (M := M) s
  haveI := hMf
  haveI : Module.Finite (ZMod p) (Fin t → (⨂[ZMod p]^s M) ⊗[ZMod p] N) := inferInstance
  obtain ⟨a, ha, hsum⟩ := exists_ne_zero_of_polyMap_eq_zero (p := p)
    (W := Fin t → (⨂[ZMod p]^s M) ⊗[ZMod p] N) (s := s) (r := r) hs
    (by rw [finrank_fin_fun]; rw [show s * (t * Module.finrank (ZMod p) ((⨂[ZMod p]^s M) ⊗[ZMod p] N))
          = t * s * Module.finrank (ZMod p) ((⨂[ZMod p]^s M) ⊗[ZMod p] N) by ring]; exact h)
    (fun e i => ((tensorExpand (p := p) s r e).rTensor N) (z i))
  refine ⟨a, ha, (surjective_foldMap_iff (p := p) (M := M) a).mpr ha, fun i => ?_⟩
  rw [rTensor_map_foldMap_apply (p := p) (M := M) (N := N) s r a]
  simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using congrFun hsum i

/-- **The shrinking lemma, paper form**: for every `s, t` there is `r₀` such that for all
`r ≥ r₀` and all `z : Fin t → (M^r)^{⊗s} ⊗ N` there is `a ≠ 0` with `φ_a` surjective and
`(φ_a^{⊗s} ⊗ id)(z_i) = 0` for all `i`. -/
theorem exists_forall_foldMap_rTensor_tensorPower_eq_zero (s t : ℕ) (hs : 1 ≤ s)
    (hM : Nontrivial M) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, ∀ z : Fin t → (⨂[ZMod p]^s (Fin r → M)) ⊗[ZMod p] N,
      ∃ a : Fin r → ZMod p, a ≠ 0 ∧ Function.Surjective (foldMap (M := M) a) ∧
        ∀ i : Fin t,
          ((PiTensorProduct.map (fun _ : Fin s => foldMap (M := M) a)).rTensor N) (z i) = 0 :=
  ⟨t * s * Module.finrank (ZMod p) ((⨂[ZMod p]^s M) ⊗[ZMod p] N) + 1,
    fun _ hr z => exists_foldMap_rTensor_tensorPower_eq_zero (p := p) (M := M) (N := N)
      hs hM (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hr) z⟩

end Shrinking

end Work.Shrinking
