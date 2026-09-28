import Mathlib
import Submission.Work.HP.MDEstimates.QuadAuxDefs
import Submission.Work.HP.MDEstimates.polar_basic

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace Work.HP.MDEstimates

/-- For a homogeneous quadratic form `Q` on `ℚ^5`, a rational point `v` on the cone `V(Q)`
and a point `w` with nonvanishing polar pairing `polQ Q v w`, the radical `R₀ = radQ Q`
(the `ℚ`-submodule, of dimension `≥ 3`) is a complement of the plane `span{v, w}`:
`R₀ ⊔ span{v,w} = ⊤` and `R₀ ⊓ span{v,w} = ⊥`. -/
theorem radSupPair (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (R₀ : Submodule ℚ (Fin 5 → ℚ)) (hR₀ : ∀ v : Fin 5 → ℚ, v ∈ R₀ ↔ v ∈ radQ Q)
    (hdim : 3 ≤ Module.finrank ℚ R₀)
    {v w : Fin 5 → ℚ} (hv : MvPolynomial.eval v Q = 0)
    (hvw : polQ Q v w ≠ 0) :
    (R₀ ⊔ Submodule.span ℚ ({v, w} : Set (Fin 5 → ℚ)) = ⊤) ∧
    (R₀ ⊓ Submodule.span ℚ ({v, w} : Set (Fin 5 → ℚ)) = ⊥) := by
  obtain ⟨hadd, hsmul, hsym, hqq, -, -⟩ := polar_basic Q hQ
  set S : Submodule ℚ (Fin 5 → ℚ) := Submodule.span ℚ ({v, w} : Set (Fin 5 → ℚ)) with hS
  -- elements of `R₀` are in the radical, hence annihilated by the polar form
  have hR0_rad : ∀ r ∈ R₀, ∀ y, polQ Q r y = 0 := fun r hr y => (hR₀ r).mp hr y
  -- `v ∉ R₀` since `polQ Q v w ≠ 0`
  have hv_notR : v ∉ R₀ := fun hvr => hvw (hR0_rad v hvr w)
  -- `polQ Q v v = Q v = 0`
  have hvv : polQ Q v v = 0 := by rw [hqq v, hv]
  -- `polQ Q 0 x = 0`
  have h00 : ∀ x : Fin 5 → ℚ, polQ Q (0 : Fin 5 → ℚ) x = 0 := by
    intro x
    simpa using hsmul (0 : ℚ) x x
  -- `v` and `w` are linearly independent
  have hlin : LinearIndependent ℚ ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hexp1 : polQ Q (s • v + t • w) v = t * polQ Q v w := by
      rw [hadd (s • v) (t • w) v, hsmul s v v, hsmul t w v, hsym w v, hvv]
      ring
    have h1 : polQ Q (s • v + t • w) v = 0 := by rw [hst, h00]
    have ht : t = 0 := by
      rw [hexp1] at h1
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hvw
    have hexp2 : polQ Q (s • v + t • w) w = s * polQ Q v w := by
      rw [hadd (s • v) (t • w) w, hsmul s v w, hsmul t w w, ht]
      ring
    have h2 : polQ Q (s • v + t • w) w = 0 := by rw [hst, h00]
    have hs : s = 0 := by
      rw [hexp2] at h2
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hvw
    exact ⟨hs, ht⟩
  -- the plane `span{v,w}` has dimension `2`
  have hrange : (Set.range ![v, w] : Set (Fin 5 → ℚ)) = {v, w} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · exact ⟨0, by simp [hz]⟩
      · exact ⟨1, by simp [hz]⟩
  have hSfin : Module.finrank ℚ ↥S = 2 := by
    rw [hS, ← hrange, finrank_span_eq_card hlin]
    simp
  -- the intersection `R₀ ⊓ span{v,w}` is trivial
  have hinf : R₀ ⊓ S = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxR, hxS⟩ := hx
    rw [hS, Submodule.mem_span_pair] at hxS
    obtain ⟨a, b, hab⟩ := hxS
    rw [← hab] at hxR
    have hb : b = 0 := by
      have h := hR0_rad _ hxR v
      rw [hadd (a • v) (b • w) v, hsmul a v v, hsmul b w v, hsym w v, hvv] at h
      have h' : b * polQ Q v w = 0 := by simpa using h
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact h''
      · exact absurd h'' hvw
    have ha : a = 0 := by
      rw [hb, zero_smul, add_zero] at hxR
      have h := hR0_rad _ hxR w
      rw [hsmul a v w] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hvw
    rw [← hab, ha, hb, zero_smul, zero_smul, add_zero]
  -- dimension count
  have hfin_inf : Module.finrank ℚ ↥(R₀ ⊓ S) = 0 := by rw [hinf, finrank_bot]
  have hsup_fin : Module.finrank ℚ ↥(R₀ ⊔ S) = Module.finrank ℚ (Fin 5 → ℚ) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq R₀ S
    rw [hfin_inf, hSfin] at h
    have hV : Module.finrank ℚ (Fin 5 → ℚ) = 5 := Module.finrank_fin_fun ℚ
    have hle := Submodule.finrank_le (R₀ ⊔ S)
    rw [hV] at hle ⊢
    omega
  exact ⟨Submodule.eq_top_of_finrank_eq hsup_fin, hinf⟩

end Work.HP.MDEstimates
