import Mathlib
import Submission.Work.DSM2p.flat_of_ker_inf_smul_top_eq_smul

/-!
# Node N2a: a quotient of a flat module by a `(f)` that is regular modulo every `I·C` is flat

Let `R → C` be a commutative `R`-algebra which is flat as an `R`-module, and let `f ∈ C` be a
non-zero-divisor *modulo every ideal* `I·C = I.map (algebraMap R C)`:

`f * c ∈ I·C → c ∈ I·C`   for all `I ⊆ R`, `c ∈ C`.

Then `C ⧸ (f)` is flat over `R`.

## Proof

By the general purity criterion `flat_of_ker_inf_smul_top_eq_smul`, it suffices to show that the
kernel `K = (f)` of the quotient map `C ↠ C ⧸ (f)` is *pure* in the `R`-module `C`, i.e.

`K ⊓ I • ⊤ = I • K`   for every ideal `I ⊆ R`.

The inclusion `⊇` is formal (`I • K ≤ K` since `K` is an ideal, and `I • K ≤ I • ⊤`).
For `⊆`, an element of `K` meeting `I • ⊤ = I·C` is `x = a * f`, and `x = f * a ∈ I·C` forces
`a ∈ I·C` by hypothesis; expanding `a` as an `I`-combination turns `x = a * f` into an
`I`-combination of multiples of `f`, i.e. into an element of `I • K`
(`mul_mem_smul_of_mem_top_mul`).  Nothing else is used.

This is node `N2a` of the design `sources/dsmap/direct_summand_m2p_h2_design.md`.
-/

namespace Work.DSM2p

/-- If `a ∈ I • ⊤` is an `R`-linear combination of elements of the `R`-algebra `C`, and `K ⊆ C`
is closed under multiplication by arbitrary elements of `C`, then `a * c ∈ I • K` for every
`c ∈ K`.

(Only the `K`-membership of the right factor survives: a summand `r • n` of `a` contributes
`(r • n) * c = r • (n * c)`, and `n * c ∈ K`.) -/
theorem mul_mem_smul_of_mem_top_mul {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    (I : Ideal R) (K : Submodule R C) (hK : ∀ (c : C), c ∈ K → ∀ (a : C), a * c ∈ K)
    {c a : C} (hc : c ∈ K) (ha : a ∈ I • (⊤ : Submodule R C)) : a * c ∈ I • K := by
  refine Submodule.smul_induction_on (I := I) (N := (⊤ : Submodule R C))
    (p := fun a => a * c ∈ I • K) ha ?_ ?_
  · intro r hr n _hn
    have heq : (r • n) * c = r • (n * c) := by
      rw [Algebra.smul_def, Algebra.smul_def]; ring
    rw [heq]
    exact Submodule.smul_mem_smul hr (hK c hc n)
  · intro x y hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy

/-- **N2a.**  `C` flat over `R` and `f` a non-zero-divisor modulo every `I·C` ⟹ `C ⧸ (f)` flat
over `R`. -/
theorem flat_quot_span_singleton_of_regular {R C : Type*} [CommRing R] [CommRing C]
    [Algebra R C] [Module.Flat R C] (f : C)
    (hreg : ∀ (I : Ideal R) (c : C), f * c ∈ I.map (algebraMap R C) →
      c ∈ I.map (algebraMap R C)) :
    Module.Flat R (C ⧸ Ideal.span {f}) := by
  classical
  set K : Submodule R C := (Ideal.span {f}).restrictScalars R with hK
  -- `K = (f)` is pure in `C`: `K ⊓ I·C = I·K`.
  have hpure : ∀ I : Ideal R, K ⊓ I • (⊤ : Submodule R C) = I • K := by
    intro I
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Submodule.mem_inf] at hx
      obtain ⟨hxK, hxI⟩ := hx
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (show x ∈ Ideal.span {f} from hxK)
      have hxI' : x ∈ Ideal.map (algebraMap R C) I := by
        simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] using hxI
      -- the cofactor `a` of `x = a * f` lies in `I·C`
      have haI : a ∈ I • (⊤ : Submodule R C) := by
        rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
        exact hreg I a (by rw [mul_comm, ha]; exact hxI')
      have hmem : a * f ∈ I • K :=
        mul_mem_smul_of_mem_top_mul I K
          (fun c hc a => Ideal.mul_mem_left (Ideal.span {f}) a (show c ∈ Ideal.span {f} from hc))
          (show f ∈ K from Ideal.subset_span (by simp)) haI
      rwa [ha] at hmem
    · intro x hx
      refine ⟨(Submodule.smul_le.mpr fun r _ n hn => ?_) hx, Submodule.smul_mono le_rfl le_top hx⟩
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left (Ideal.span {f}) (algebraMap R C r) (show n ∈ Ideal.span {f} from hn)
  have hker : ∀ I : Ideal R,
      (Submodule.mkQ K).ker ⊓ I • (⊤ : Submodule R C) = I • (Submodule.mkQ K).ker := by
    intro I
    rw [Submodule.ker_mkQ]
    exact hpure I
  have hgoal : Module.Flat R (C ⧸ K) :=
    flat_of_ker_inf_smul_top_eq_smul K.mkQ K.mkQ_surjective hker
  rw [hK] at hgoal
  exact hgoal

end Work.DSM2p
