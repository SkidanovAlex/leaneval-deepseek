import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Auxi.SimplexCover

/-!
# A9 aux: subdivision faces lying in a union of coarse faces

`exists_coarse_face_of_simp_subset`: if the simplex on a face `s` of a subdivision of `K` is
contained in a union `L` of faces of `K`, then `simp s` is contained in a *single* face `τ ∈ K.faces`
with `simp τ ⊆ L`.  This is what makes `Tame`/`SmoothChart` (which quantify over faces of the
*coarse* complex) transfer to a subdivided complex.

Proof: let `σ ∈ K.faces` be a carrier of `s` (from `Subdivides`), and let `b` be the barycentre of
`s`.  Since `b ∈ simp s ⊆ L`, there is `τ ∈ K.faces` with `simp τ ⊆ L` and `b ∈ simp τ`.  Writing
the σ-coordinates of each vertex of `s` (`Finset.mem_convexHull'`) and comparing the *mean* of those
coordinates with the σ-coordinates of `b` (uniqueness of barycentric coordinates on the affinely
independent face `σ`, `AffineIndependent.eq_of_sum_eq_sum_subtype`), one gets that every vertex of
`s` lies in `simp τ`; convexity of `simp τ` finishes.
-/

open Set Metric PL Finset

namespace Work.Engulf

variable {N : ℕ}

/-- The barycentre is the mean of the `σ`-coordinates of the vertices. -/
theorem bary_eq_sum_mean {σ s : Finset (E N)} (Λ : ∀ v ∈ s, E N → ℝ)
    (h2 : ∀ v hv, ∑ w ∈ σ, Λ v hv w • w = v) :
    ∑ w ∈ σ, (((s.card : ℝ))⁻¹ * ∑ v ∈ s.attach, Λ v.1 v.2 w) • w = bary s := by
  rw [Finset.sum_congr rfl (fun w _ => by rw [mul_smul]), ← Finset.smul_sum]
  congr 1
  rw [Finset.sum_congr rfl (fun w _ => by rw [Finset.sum_smul]), Finset.sum_comm,
    Finset.sum_congr rfl (fun v _ => h2 v.1 v.2)]
  simpa using Finset.sum_attach s (fun v : E N => v)

/-- **Carrier lemma.** A simplex of a subdivision contained in a union of coarse faces lies in a
single coarse face inside that union. -/
theorem exists_coarse_face_of_simp_subset (S : SubdivTools N) {r : ℕ} {K : Cx N}
    {hK : K.faces.Finite} {L : Set (E N)} (hLK : IsSubSp K L) {s : Finset (E N)}
    (hs : s ∈ (S.sdIter r K hK).faces) (hsL : simp s ⊆ L) :
    ∃ τ ∈ K.faces, simp τ ⊆ L ∧ simp s ⊆ simp τ := by
  classical
  obtain ⟨T, hT, hTL⟩ := (isSubSp_iff K L).1 hLK
  obtain ⟨σ, hσ, hσs⟩ := (S.subdiv r K hK).2 s hs
  have hsne : s.Nonempty := (S.sdIter r K hK).nonempty_of_mem_faces hs
  have hcard : (s.card : ℝ) ≠ 0 := by simp [Finset.card_ne_zero.2 hsne]
  have hbL : bary s ∈ L := hsL (bary_mem_simp hsne)
  rw [hTL] at hbL
  obtain ⟨τ, hτT, hbτ⟩ := mem_iUnion₂.1 hbL
  have hτK : τ ∈ K.faces := hT hτT
  refine ⟨τ, hτK, ?_, ?_⟩
  · rw [hTL]
    exact fun x hx => mem_iUnion₂.2 ⟨τ, hτT, hx⟩
  have hbσ : bary s ∈ simp σ := hσs (bary_mem_simp hsne)
  have hbυ : bary s ∈ simp (τ ∩ σ) := by
    rw [← simp_inter hτK hσ]
    exact ⟨hbτ, hbσ⟩
  obtain ⟨ρ, hρ0, hρ1, hρ2⟩ := Finset.mem_convexHull'.1 hbυ
  have hcoef : ∀ v ∈ s, ∃ lm : E N → ℝ, (∀ w ∈ σ, 0 ≤ lm w) ∧ ∑ w ∈ σ, lm w = 1 ∧
      ∑ w ∈ σ, lm w • w = v := fun v hv => Finset.mem_convexHull'.1 (hσs (subset_simp hv))
  choose Λ hΛ0 hΛ1 hΛ2 using hcoef
  set ν : E N → ℝ := fun w => ((s.card : ℝ))⁻¹ * ∑ v ∈ s.attach, Λ v.1 v.2 w with hν
  set ρ' : E N → ℝ := fun w => if w ∈ τ ∩ σ then ρ w else 0 with hρ'
  have hsum1 : ∑ w ∈ σ, ν w = ∑ w ∈ σ, ρ' w := by
    have hν1 : ∑ w ∈ σ, ν w = 1 := by
      rw [hν, ← Finset.mul_sum, Finset.sum_comm,
        Finset.sum_congr rfl (fun v _ => hΛ1 v.1 v.2),
        Finset.sum_const, nsmul_eq_mul, Finset.card_attach, mul_one, inv_mul_cancel₀ hcard]
    have hρ'1 : ∑ w ∈ σ, ρ' w = 1 := by
      rw [hρ', Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr Finset.inter_subset_right, hρ1]
    rw [hν1, hρ'1]
  have hsum2 : ∑ w ∈ σ, ν w • w = ∑ w ∈ σ, ρ' w • w := by
    have hν2 : ∑ w ∈ σ, ν w • w = bary s := by
      rw [hν]
      exact bary_eq_sum_mean Λ hΛ2
    have hstep : ∑ w ∈ σ, ρ' w • w = ∑ w ∈ σ, (if w ∈ τ ∩ σ then ρ w • w else 0) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [hρ']
      by_cases h : w ∈ τ ∩ σ <;> simp [h]
    have hρ'2 : ∑ w ∈ σ, ρ' w • w = bary s := by
      rw [hstep, Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr Finset.inter_subset_right, hρ2]
    rw [hν2, hρ'2]
  have huniq := AffineIndependent.eq_of_sum_eq_sum_subtype (K.indep hσ) hsum1 hsum2
  have hvert : ∀ v ∈ s, v ∈ simp τ := by
    intro v hv
    -- the σ-coordinates of `v` vanish off `τ`: the mean of all coordinates is `b`
    have hcoe : ∀ w ∈ σ, w ∉ τ ∩ σ → Λ v hv w = 0 := by
      intro w hwσ hwnτ
      have hνw : ν w = 0 := by
        have h1 : ρ' w = 0 := by rw [hρ']; simp [Finset.mem_inter, hwnτ]
        rw [huniq w hwσ, h1]
      have hsum0 : ∑ x ∈ s.attach, Λ x.1 x.2 w = 0 := by
        rw [hν] at hνw
        rcases mul_eq_zero.mp hνw with h | h
        · exact absurd h (inv_ne_zero hcard)
        · exact h
      have hle : Λ v hv w ≤ ∑ x ∈ s.attach, Λ x.1 x.2 w :=
        Finset.single_le_sum (fun i _ => hΛ0 i.1 i.2 w hwσ) (Finset.mem_attach s ⟨v, hv⟩)
      have h0 := hΛ0 v hv w hwσ
      linarith
    have hmem : v ∈ simp (τ ∩ σ) := by
      refine Finset.mem_convexHull'.2 ⟨fun w => if w ∈ τ ∩ σ then Λ v hv w else 0, ?_, ?_, ?_⟩
      · intro w _
        show 0 ≤ (if w ∈ τ ∩ σ then Λ v hv w else 0)
        by_cases h : w ∈ τ ∩ σ
        · rw [if_pos h]; exact hΛ0 v hv w (Finset.mem_of_mem_inter_right h)
        · rw [if_neg h]
      · have hstep : ∑ w ∈ (τ ∩ σ), (if w ∈ τ ∩ σ then Λ v hv w else 0)
            = ∑ w ∈ (τ ∩ σ), Λ v hv w := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [if_pos hw]
        rw [hstep, Finset.sum_subset (s₁ := τ ∩ σ) (s₂ := σ) Finset.inter_subset_right
          (fun w hw hw' => hcoe w hw hw'), hΛ1]
      · have hstep : ∑ w ∈ (τ ∩ σ), (if w ∈ τ ∩ σ then Λ v hv w else 0) • w
            = ∑ w ∈ (τ ∩ σ), Λ v hv w • w := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [if_pos hw]
        rw [hstep, Finset.sum_subset (s₁ := τ ∩ σ) (s₂ := σ) Finset.inter_subset_right
          (fun w hw hw' => by rw [hcoe w hw hw', zero_smul]), hΛ2]
    exact simp_mono Finset.inter_subset_left hmem
  have : (s : Set (E N)) ⊆ simp τ := fun v hv => hvert v (Finset.mem_coe.mp hv)
  calc simp s = convexHull ℝ (s : Set (E N)) := rfl
    _ ⊆ convexHull ℝ (simp τ) := convexHull_mono this
    _ = simp τ := Convex.convexHull_eq (convex_simp τ)

end Work.Engulf
