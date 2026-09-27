import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.bary_inj

namespace Work.PL.Shell

open Set Metric Finset
open scoped BigOperators

noncomputable section

variable {N : ℕ}

/-- Auxiliary "level" function of a chain `C` with weights `lam`: for `A ∈ C`,
`chD C lam A` is the common value of the `v`-coordinates (`chP`) over the "new part"
of `A` inside the chain. -/
def chD (C : Finset (Finset (PL.E N))) (lam : Finset (PL.E N) → ℝ) (A : Finset (PL.E N)) : ℝ :=
  ∑ A' ∈ C, if A ⊆ A' then lam A' / (A'.card : ℝ) else 0

/-- `chP C lam v` is the `v`-coordinate of the point `∑_{A ∈ C} lam A • bary A`:
the barycentric coordinate of that point at the vertex `v`. -/
def chP (C : Finset (Finset (PL.E N))) (lam : Finset (PL.E N) → ℝ) (v : PL.E N) : ℝ :=
  ∑ A ∈ C, if v ∈ A then lam A / (A.card : ℝ) else 0

lemma chD_le_chP {C : Finset (Finset (PL.E N))} {lam : Finset (PL.E N) → ℝ}
    (h0 : ∀ A ∈ C, 0 ≤ lam A)
    {A : Finset (PL.E N)} (hA : A ∈ C) {v : PL.E N} (hv : v ∈ A) :
    chD C lam A ≤ chP C lam v := by
  rw [chD, chP]
  apply Finset.sum_le_sum
  intro A' hA'
  by_cases hvA' : v ∈ A'
  · rw [if_pos hvA']
    by_cases hsub : A ⊆ A'
    · rw [if_pos hsub]
    · rw [if_neg hsub]
      exact div_nonneg (h0 A' hA') (Nat.cast_nonneg _)
  · have hnot : ¬ A ⊆ A' := fun h => hvA' (h hv)
    rw [if_neg hnot, if_neg hvA']

lemma chP_lt_chD {C : Finset (Finset (PL.E N))} {lam : Finset (PL.E N) → ℝ}
    (hc : ∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A) (h0 : ∀ A ∈ C, 0 ≤ lam A)
    (hne : ∀ A ∈ C, A.Nonempty)
    {A : Finset (PL.E N)} (hA : A ∈ C) (hApos : 0 < lam A) {v : PL.E N} (hv : v ∉ A) :
    chP C lam v < chD C lam A := by
  rw [chP, chD]
  apply Finset.sum_lt_sum
  · intro A' hA'
    by_cases hvA' : v ∈ A'
    · have hsub : A ⊆ A' := by
        rcases hc A hA A' hA' with h | h
        · exact h
        · exact absurd (h hvA') hv
      rw [if_pos hvA', if_pos hsub]
    · rw [if_neg hvA']
      by_cases hAA' : A ⊆ A'
      · rw [if_pos hAA']
        exact div_nonneg (h0 A' hA') (Nat.cast_nonneg _)
      · rw [if_neg hAA']
  · refine ⟨A, hA, ?_⟩
    rw [if_neg hv, if_pos (Finset.Subset.refl A)]
    exact div_pos hApos (by exact_mod_cast (hne A hA).card_pos)

/-- For a chain `C` and a vertex `v` lying in some member of `C`, there is a unique
smallest member `A0` of `C` containing `v`, and the coordinate `chP C lam v` equals
`chD C lam A0`. -/
lemma chP_eq_chD_min {C : Finset (Finset (PL.E N))} {lam : Finset (PL.E N) → ℝ}
    (hc : ∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A)
    {v : PL.E N} (hv : ∃ A ∈ C, v ∈ A) :
    ∃ A0 ∈ C, v ∈ A0 ∧ (∀ A ∈ C, v ∈ A → A0 ⊆ A) ∧ chP C lam v = chD C lam A0 := by
  classical
  obtain ⟨A0, hA0R, hA0min⟩ :=
    Finset.exists_min_image (C.filter (fun A => v ∈ A)) Finset.card
      (by obtain ⟨A, hA, hvA⟩ := hv; exact ⟨A, Finset.mem_filter.mpr ⟨hA, hvA⟩⟩)
  have hA0C : A0 ∈ C := (Finset.mem_filter.mp hA0R).1
  have hA0v : v ∈ A0 := (Finset.mem_filter.mp hA0R).2
  have hmin : ∀ A ∈ C, v ∈ A → A0 ⊆ A := by
    intro A hAC hvA
    have hAR : A ∈ C.filter (fun A => v ∈ A) := Finset.mem_filter.mpr ⟨hAC, hvA⟩
    have hcard : A0.card ≤ A.card := hA0min A hAR
    rcases hc A0 hA0C A hAC with h | h
    · exact h
    · have hAeq : A = A0 := Finset.eq_of_subset_of_card_le h hcard
      rw [hAeq]
  have heq : chP C lam v = chD C lam A0 := by
    rw [chP, chD]
    apply Finset.sum_congr rfl
    intro A' hA'
    by_cases hvA' : v ∈ A'
    · rw [if_pos hvA', if_pos (hmin A' hA' hvA')]
    · rw [if_neg hvA', if_neg (fun hsub => hvA' (hsub hA0v))]
  exact ⟨A0, hA0C, hA0v, hmin, heq⟩

/-- The nonempty positive level sets of the coordinate function `chP C mu` are exactly the
members of the chain `C` carrying positive weight.  In particular every such level set is a
member of `C`. -/
lemma level_mem {Δ : Finset (PL.E N)} {C : Finset (Finset (PL.E N))} {mu : Finset (PL.E N) → ℝ}
    (hc : ∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A) (h0 : ∀ A ∈ C, 0 ≤ mu A)
    (hsub : ∀ A ∈ C, A ⊆ Δ) {c : ℝ} (hcpos : 0 < c)
    (hLne : (Δ.filter (fun v => c ≤ chP C mu v)).Nonempty) :
    ∃ B ∈ C, B = Δ.filter (fun v => c ≤ chP C mu v) := by
  classical
  have key : ∀ v ∈ Δ.filter (fun v => c ≤ chP C mu v),
      ∃ A ∈ C, v ∈ A ∧ c ≤ chD C mu A := by
    intro v hvL
    have hvL' := Finset.mem_filter.mp hvL
    have hcv : c ≤ chP C mu v := hvL'.2
    have hpos : 0 < chP C mu v := lt_of_lt_of_le hcpos hcv
    have hvU : ∃ A ∈ C, v ∈ A := by
      by_contra h
      push_neg at h
      have hz : chP C mu v = 0 := Finset.sum_eq_zero (fun A hA => by simp [h A hA])
      rw [hz] at hpos
      exact absurd hpos (lt_irrefl 0)
    obtain ⟨A0, hA0C, hA0v, -, hA0eq⟩ := chP_eq_chD_min (lam := mu) hc hvU
    refine ⟨A0, hA0C, hA0v, ?_⟩
    rw [← hA0eq]
    exact hcv
  have hDne : (C.filter (fun B => c ≤ chD C mu B)).Nonempty := by
    obtain ⟨v, hvL⟩ := hLne
    obtain ⟨A, hA, -, hAc⟩ := key v hvL
    exact ⟨A, Finset.mem_filter.mpr ⟨hA, hAc⟩⟩
  obtain ⟨Bstar, hBstarD, hBstarmax⟩ :=
    Finset.exists_max_image (C.filter (fun B => c ≤ chD C mu B)) Finset.card hDne
  have hBstarC : Bstar ∈ C := (Finset.mem_filter.mp hBstarD).1
  have hBstarval : c ≤ chD C mu Bstar := (Finset.mem_filter.mp hBstarD).2
  refine ⟨Bstar, hBstarC, ?_⟩
  ext v
  rw [Finset.mem_filter]
  constructor
  · intro hvBstar
    exact ⟨hsub Bstar hBstarC hvBstar, le_trans hBstarval (chD_le_chP h0 hBstarC hvBstar)⟩
  · rintro ⟨hvΔ, hcv⟩
    obtain ⟨A, hAC, hvA, hAc⟩ := key v (Finset.mem_filter.mpr ⟨hvΔ, hcv⟩)
    have hAD : A ∈ C.filter (fun B => c ≤ chD C mu B) := Finset.mem_filter.mpr ⟨hAC, hAc⟩
    have hcard : A.card ≤ Bstar.card := hBstarmax A hAD
    rcases hc A hAC Bstar hBstarC with h | h
    · exact h hvA
    · have hAeq : Bstar = A := Finset.eq_of_subset_of_card_le h hcard
      rw [hAeq]; exact hvA

/-- The sum of the coordinates of `∑_{A ∈ C} lam A • bary A` equals the total weight. -/
lemma sum_chP {Δ : Finset (PL.E N)} {C : Finset (Finset (PL.E N))} {lam : Finset (PL.E N) → ℝ}
    (hsub : ∀ A ∈ C, A ⊆ Δ) (hne : ∀ A ∈ C, A.Nonempty) :
    ∑ v ∈ Δ, chP C lam v = ∑ A ∈ C, lam A := by
  simp only [chP]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Finset.sum_subset (hsub A hA) (fun v _ hvA => by rw [if_neg hvA])]
  have hcongr : ∑ v ∈ A, (if v ∈ A then lam A / (A.card : ℝ) else 0)
      = ∑ v ∈ A, lam A / (A.card : ℝ) :=
    Finset.sum_congr rfl (fun v hv => if_pos hv)
  rw [hcongr, Finset.sum_const, nsmul_eq_mul, ← mul_div_assoc]
  have hc0 : (A.card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hne A hA).card_pos)
  rw [mul_div_cancel_left₀ _ hc0]

/-- `∑_{A ∈ C} lam A • bary A` written as a combination of the ambient vertices `Δ`. -/
lemma sum_chP_smul {Δ : Finset (PL.E N)} {C : Finset (Finset (PL.E N))} {lam : Finset (PL.E N) → ℝ}
    (hsub : ∀ A ∈ C, A ⊆ Δ) :
    ∑ v ∈ Δ, chP C lam v • v = ∑ A ∈ C, lam A • bary A := by
  simp only [chP]
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Finset.sum_subset (hsub A hA) (fun v _ hvA => by rw [if_neg hvA, zero_smul])]
  have hcongr : ∑ v ∈ A, (if v ∈ A then lam A / (A.card : ℝ) else 0) • v
      = ∑ v ∈ A, (lam A / (A.card : ℝ)) • v :=
    Finset.sum_congr rfl (fun v hv => by rw [if_pos hv])
  have hR : lam A • bary A = ∑ v ∈ A, (lam A / (A.card : ℝ)) • v := by
    rw [bary, ← mul_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun v _ => by rw [div_eq_mul_inv])
  rw [hcongr, hR]

theorem convexHull_inter_bary {N : ℕ} {Δ : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    {C C' : Finset (Finset (PL.E N))}
    (hC : ∀ A ∈ C, A.Nonempty ∧ A ⊆ Δ) (hC' : ∀ A ∈ C', A.Nonempty ∧ A ⊆ Δ)
    (hc : ∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A) (hc' : ∀ A ∈ C', ∀ B ∈ C', A ⊆ B ∨ B ⊆ A) :
    PL.simp (C.image Work.PL.Shell.bary) ∩ PL.simp (C'.image Work.PL.Shell.bary)
      = PL.simp ((C ∩ C').image Work.PL.Shell.bary) := by
  classical
  simp only [PL.simp]
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxV, hxW⟩
    obtain ⟨w, hw0, hwsum, hwsmul⟩ := Finset.mem_convexHull'.mp hxV
    obtain ⟨w', hw0', hwsum', hwsmul'⟩ := Finset.mem_convexHull'.mp hxW
    set lam : Finset (PL.E N) → ℝ := fun A => w (bary A) with hlam
    set mu : Finset (PL.E N) → ℝ := fun B => w' (bary B) with hmu
    have hinjC : Set.InjOn bary (↑C : Set (Finset (PL.E N))) := by
      intro A hA B hB hAB
      have hAc := hC A (by simpa using hA)
      have hBc := hC B (by simpa using hB)
      exact bary_inj hΔ hAc.1 hBc.1 hAc.2 hBc.2 hAB
    have hinjC' : Set.InjOn bary (↑C' : Set (Finset (PL.E N))) := by
      intro A hA B hB hAB
      have hAc := hC' A (by simpa using hA)
      have hBc := hC' B (by simpa using hB)
      exact bary_inj hΔ hAc.1 hBc.1 hAc.2 hBc.2 hAB
    have h0 : ∀ A ∈ C, 0 ≤ lam A := by
      intro A hA
      simp only [hlam]
      exact hw0 (bary A) (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
    have h0' : ∀ A ∈ C', 0 ≤ mu A := by
      intro A hA
      simp only [hmu]
      exact hw0' (bary A) (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
    have hne : ∀ A ∈ C, A.Nonempty := fun A hA => (hC A hA).1
    have hne' : ∀ A ∈ C', A.Nonempty := fun A hA => (hC' A hA).1
    have hsubC : ∀ A ∈ C, A ⊆ Δ := fun A hA => (hC A hA).2
    have hsubC' : ∀ A ∈ C', A ⊆ Δ := fun A hA => (hC' A hA).2
    have hlamsum : ∑ A ∈ C, lam A = 1 := by
      simp only [hlam]
      exact (Finset.sum_image (f := w) hinjC).symm.trans hwsum
    have hmusum : ∑ A ∈ C', mu A = 1 := by
      simp only [hmu]
      exact (Finset.sum_image (f := w') hinjC').symm.trans hwsum'
    have hlamsmul : ∑ A ∈ C, lam A • bary A = x := by
      simp only [hlam]
      exact (Finset.sum_image (f := fun y => w y • y) hinjC).symm.trans hwsmul
    have hmusmul : ∑ A ∈ C', mu A • bary A = x := by
      simp only [hmu]
      exact (Finset.sum_image (f := fun y => w' y • y) hinjC').symm.trans hwsmul'
    -- affine independence of `Δ` gives that the two coordinate functions agree
    have hpq : ∀ v ∈ Δ, chP C lam v = chP C' mu v := by
      have hsp : ∑ v ∈ Δ, chP C lam v = 1 := by
        rw [sum_chP hsubC hne]; exact hlamsum
      have hsq : ∑ v ∈ Δ, chP C' mu v = 1 := by
        rw [sum_chP hsubC' hne']; exact hmusum
      have hvp : ∑ v ∈ Δ, chP C lam v • v = x := by
        rw [sum_chP_smul hsubC]; exact hlamsmul
      have hvq : ∑ v ∈ Δ, chP C' mu v • v = x := by
        rw [sum_chP_smul hsubC']; exact hmusmul
      exact hΔ.eq_of_sum_eq_sum_subtype (by rw [hsp, hsq]) (by rw [hvp, hvq])
    -- every member of `C` with positive weight is a positive level set, hence lies in `C'`
    have hAlvl : ∀ A ∈ C, 0 < lam A → A ∈ C' := by
      intro A hAC hApos
      have hlc : A = Δ.filter (fun v => chD C lam A ≤ chP C lam v) := by
        ext v
        rw [Finset.mem_filter]
        constructor
        · intro hv
          exact ⟨hsubC A hAC hv, chD_le_chP h0 hAC hv⟩
        · rintro ⟨-, hle⟩
          by_contra hv
          exact absurd hle (not_le.mpr (chP_lt_chD hc h0 hne hAC hApos hv))
      have hcpos : 0 < chD C lam A := by
        have hnonneg : ∀ A' ∈ C, 0 ≤ (if A ⊆ A' then lam A' / (A'.card : ℝ) else 0) := by
          intro A' hA'
          by_cases h : A ⊆ A'
          · rw [if_pos h]; exact div_nonneg (h0 A' hA') (Nat.cast_nonneg _)
          · rw [if_neg h]
        have hle := Finset.single_le_sum hnonneg hAC
        rw [chD]
        refine lt_of_lt_of_le ?_ hle
        rw [if_pos (Finset.Subset.refl A)]
        exact div_pos hApos (by exact_mod_cast (hne A hAC).card_pos)
      have hfilter : Δ.filter (fun v => chD C lam A ≤ chP C' mu v)
          = Δ.filter (fun v => chD C lam A ≤ chP C lam v) := by
        apply Finset.filter_congr
        intro v hv
        rw [hpq v hv]
      have hAL : Δ.filter (fun v => chD C lam A ≤ chP C' mu v) = A :=
        hfilter.trans hlc.symm
      obtain ⟨B, hBC', hBeq⟩ :=
        level_mem hc' h0' hsubC' hcpos (by rw [hAL]; exact (hC A hAC).1)
      have hAB : A = B := by rw [← hAL, ← hBeq]
      rw [← hAB] at hBC'
      exact hBC'
    -- the convex combination only involves members of `C ∩ C'`
    have hsum_inter : ∑ A ∈ C ∩ C', lam A = 1 := by
      rw [← hlamsum]
      apply Finset.sum_subset Finset.inter_subset_left
      intro A hAC hAnI
      have hz : lam A = 0 := by
        by_contra hne0
        have hpos : 0 < lam A := lt_of_le_of_ne (h0 A hAC) (Ne.symm hne0)
        exact hAnI (Finset.mem_inter.mpr ⟨hAC, hAlvl A hAC hpos⟩)
      exact hz
    have hsmul_inter : ∑ A ∈ C ∩ C', lam A • bary A = x := by
      rw [← hlamsmul]
      apply Finset.sum_subset Finset.inter_subset_left
      intro A hAC hAnI
      have hz : lam A = 0 := by
        by_contra hne0
        have hpos : 0 < lam A := lt_of_le_of_ne (h0 A hAC) (Ne.symm hne0)
        exact hAnI (Finset.mem_inter.mpr ⟨hAC, hAlvl A hAC hpos⟩)
      rw [hz, zero_smul]
    -- build the convex-combination certificate on the image
    set U : Finset (PL.E N) := (C ∩ C').image bary with hU
    have hinjI : Set.InjOn bary (↑(C ∩ C') : Set (Finset (PL.E N))) := by
      intro A hA B hB hAB
      have hAI : A ∈ C ∩ C' := by simpa using hA
      have hBI : B ∈ C ∩ C' := by simpa using hB
      have hAc := hC A (Finset.mem_inter.mp hAI).1
      have hBc := hC B (Finset.mem_inter.mp hBI).1
      exact bary_inj hΔ hAc.1 hBc.1 hAc.2 hBc.2 hAB
    set wf : PL.E N → ℝ := fun y => ∑ B ∈ C ∩ C', if bary B = y then lam B else 0 with hwf
    have hwf_nonneg : ∀ y ∈ U, 0 ≤ wf y := by
      intro y hy
      simp only [hwf]
      apply Finset.sum_nonneg
      intro B hB
      by_cases h : bary B = y
      · rw [if_pos h]; exact h0 B (Finset.mem_inter.mp hB).1
      · rw [if_neg h]
    have hwf_eval : ∀ A ∈ C ∩ C', wf (bary A) = lam A := by
      intro A hA
      simp only [hwf]
      have heq : (∑ B ∈ C ∩ C', (if bary B = bary A then lam B else 0))
          = (if bary A = bary A then lam A else 0) :=
        Finset.sum_eq_single A
          (fun B hB hBA => by
            rw [if_neg]
            intro hbary
            exact hBA (hinjI (by simpa using hB) (by simpa using hA) hbary))
          (fun hAnI => absurd hA hAnI)
      rw [heq, if_pos rfl]
    have hwf_sum : ∑ y ∈ U, wf y = 1 := by
      rw [hU, Finset.sum_image hinjI]
      exact (Finset.sum_congr rfl (fun A hA => hwf_eval A hA)).trans hsum_inter
    have hwf_smul : ∑ y ∈ U, wf y • y = x := by
      rw [hU, Finset.sum_image hinjI]
      refine (Finset.sum_congr rfl (fun A hA => by rw [hwf_eval A hA])).trans ?_
      exact hsmul_inter
    exact Finset.mem_convexHull'.mpr ⟨wf, hwf_nonneg, hwf_sum, hwf_smul⟩
  · intro x hx
    refine ⟨convexHull_mono ?_ hx, convexHull_mono ?_ hx⟩
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_image] at hy ⊢
      obtain ⟨A, hA, hAy⟩ := hy
      exact ⟨A, (Finset.mem_inter.mp hA).1, hAy⟩
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_image] at hy ⊢
      obtain ⟨A, hA, hAy⟩ := hy
      exact ⟨A, (Finset.mem_inter.mp hA).2, hAy⟩


end

end Work.PL.Shell
