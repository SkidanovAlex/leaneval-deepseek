import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.PeriodicTiling

open Filter Bornology MeasureTheory
open scoped Pointwise

set_option linter.unusedSimpArgs false

/-- Given an additive commutative group `G`, `F` and `A` tile `G` if the
translates of `F` by elements of `A` form a partition of `G`.  This is the
definition used by the periodic tiling conjecture; it is stated here in the
commons so that the lemma below does not depend on the problem-specific
`ChallengeDeps` module. -/
abbrev IsTiling {G : Type*} [AddCommGroup G] (F A : Set G) : Prop :=
  AddSubgroup.IsComplement A F

/-- A continuous tiling of `ℝ^d` by translates of `σ` along `Λ`, up to null
sets.  This is the definition used by the periodic tiling conjecture; it is
stated here in the commons so that the lemma below does not depend on the
problem-specific `ChallengeDeps` module. -/
def IsContinuousTiling {d : ℕ} (σ Λ : Set (Fin d → ℝ)) : Prop :=
  ∀ᵐ x, ∃! v ∈ Λ, x ∈ (v +ᵥ σ)

theorem isContinuousTiling_of_isTiling_lift
    {d : ℕ} {R : Set (Fin d → ℝ)}
    (hR : IsContinuousTiling R {x : Fin d → ℝ | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)})
    {F A : Set (Fin d → ℤ)} (h : IsTiling F A) :
    IsContinuousTiling
      ((fun z : Fin d → ℤ => fun i : Fin d => (z i : ℝ)) '' F + R)
      ((fun z : Fin d → ℤ => fun i : Fin d => (z i : ℝ)) '' A) := by
  let e : (Fin d → ℤ) →+ (Fin d → ℝ) :=
    AddMonoidHom.piMap (fun _ : Fin d => Int.castAddHom ℝ)
  have he_inj : Function.Injective e := by
    intro a b hab
    apply funext
    intro i
    have hi : ((Int.castAddHom ℝ) (a i) : ℝ) = (Int.castAddHom ℝ) (b i) := congr_fun hab i
    exact Int.cast_injective hi
  let L : Set (Fin d → ℝ) := {x | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)}
  have hR' : ∀ᵐ x, ∃! u, u ∈ L ∧ x ∈ u +ᵥ R := by
    simpa [IsContinuousTiling, L] using hR
  change IsContinuousTiling (e '' F + R) (e '' A)
  unfold IsContinuousTiling
  refine hR'.mono ?_
  intro x hx
  rcases hx with ⟨u, hu, hu_uniq⟩
  rcases hu with ⟨huL, hxu⟩
  rcases huL with ⟨z, hz⟩
  have huz : u = e z := by
    ext i
    simpa [e] using hz i
  have hxu' : x ∈ e z +ᵥ R := by
    simpa [huz] using hxu
  obtain ⟨⟨⟨a, haA⟩, ⟨f, hfF⟩⟩, hsum, hpair_uniq⟩ := h.existsUnique z
  have hesum : e z = e a + e f := by
    rw [← hsum]
    exact map_add e a f
  have hx1 : x ∈ (e a + e f) +ᵥ R := by
    rw [← hesum]
    exact hxu'
  refine ⟨e a, ?_, ?_⟩
  · constructor
    · exact ⟨a, haA, rfl⟩
    · rw [Set.mem_vadd_set]
      rw [Set.mem_vadd_set] at hx1
      rcases hx1 with ⟨r, hr, hxeq⟩
      refine ⟨e f + r, ?_, ?_⟩
      · rw [Set.mem_add]
        exact ⟨e f, ⟨f, hfF, rfl⟩, r, hr, rfl⟩
      · simpa [vadd_eq_add, add_assoc] using hxeq
  · intro v hv
    rcases hv with ⟨hvA, hvx⟩
    rcases hvA with ⟨a', ha'A, ha'v⟩
    rw [Set.mem_vadd_set] at hvx
    rcases hvx with ⟨y, hy, hxeq_v⟩
    rw [Set.mem_add] at hy
    rcases hy with ⟨q, hq, r, hr, hyeq⟩
    rcases hq with ⟨f', hf'F, hqf'⟩
    have hx2 : x ∈ (e a' + e f') +ᵥ R := by
      rw [Set.mem_vadd_set]
      refine ⟨r, hr, ?_⟩
      rw [← hxeq_v, ← ha'v, ← hyeq, ← hqf']
      simp [vadd_eq_add, add_assoc]
    have hx2' : x ∈ e (a' + f') +ᵥ R := by
      simpa [map_add e a' f', add_comm, add_left_comm, add_assoc] using hx2
    have hmem : e (a' + f') ∈ L := by
      dsimp [L]
      exact ⟨a' + f', by intro i; rfl⟩
    have hu_eq : e (a' + f') = u := by
      apply hu_uniq
      exact ⟨hmem, hx2'⟩
    have hz_eq : a' + f' = z := by
      apply he_inj
      rw [hu_eq, huz]
    have hpair_eq : ((⟨a', ha'A⟩, ⟨f', hf'F⟩) : ↥A × ↥F) = ((⟨a, haA⟩, ⟨f, hfF⟩) : ↥A × ↥F) := by
      apply hpair_uniq
      simpa using hz_eq
    have ha_eq : a' = a := by
      exact Subtype.ext_iff.mp (Prod.ext_iff.mp hpair_eq).1
    rw [← ha'v]
    exact congrArg e ha_eq

end Commons.PeriodicTiling