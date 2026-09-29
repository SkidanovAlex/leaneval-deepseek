import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.MainP.crtDefs
import Submission.Work.Main.crt.Pcr_inj
import Submission.Work.Main.crt.Pcr_lt
import Submission.Work.Main.crt.Pinv_spec

/-!
# The CRT reindexing is a bijection of `[0, ∏ ss)`

`HvdH.crtIdx` is literally `Work.Main.Pcr`, so the bijectivity facts proved there
(`Pcr_lt`, `Pcr_inj`, `Pinv_spec`) transfer; here they are packaged as:
`crtIdx_lt`, `crtIdx_inj`, `crtIdx_surj`, the inverse laws for `crtPinv`, and the distinctness /
range properties of the label lists `sigmaList` and `crtQ` used by the label-and-sort word.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## `crtIdx` versus `Pcr` -/

theorem crtIdx_eq_Pcr (ss : List ℕ) (m : ℕ) : crtIdx ss m = Work.Main.Pcr ss m := by
  induction ss with
  | nil => simp [Work.Main.Pcr]
  | cons s ss ih => simp [Work.Main.Pcr, ih]

theorem crtIdx_lt {ss : List ℕ} (hpos : ∀ s ∈ ss, 0 < s) (m : ℕ) : crtIdx ss m < ss.prod := by
  rw [crtIdx_eq_Pcr]; exact Work.Main.crt.Pcr_lt hpos m

theorem crtIdx_inj {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {m₁ m₂ : ℕ} (h₁ : m₁ < ss.prod) (h₂ : m₂ < ss.prod) (h : crtIdx ss m₁ = crtIdx ss m₂) :
    m₁ = m₂ := by
  simp only [crtIdx_eq_Pcr] at h
  exact Work.Main.crt.Pcr_inj hcop hpos h₁ h₂ h

/-! ## Surjectivity, and the inverse `crtPinv` -/

theorem crtIdx_surj {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {j : ℕ} (hj : j < ss.prod) : ∃ m, m < ss.prod ∧ crtIdx ss m = j := by
  let f : Fin ss.prod → Fin ss.prod := fun m => ⟨crtIdx ss m.val, crtIdx_lt hpos m.val⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    exact crtIdx_inj hcop hpos a.isLt b.isLt (congrArg Fin.val hab)
  obtain ⟨m, hm⟩ := Finite.surjective_of_injective hf ⟨j, hj⟩
  exact ⟨m.val, m.isLt, by simpa [f] using congrArg Fin.val hm⟩

theorem crtPinv_lt {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {j : ℕ} (hj : j < ss.prod) : crtPinv ss j < ss.prod :=
  (crtPinv_spec (crtIdx_surj hcop hpos hj)).1

theorem crtIdx_crtPinv {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {j : ℕ} (hj : j < ss.prod) : crtIdx ss (crtPinv ss j) = j :=
  (crtPinv_spec (crtIdx_surj hcop hpos hj)).2

theorem crtPinv_crtIdx {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {m : ℕ} (hm : m < ss.prod) : crtPinv ss (crtIdx ss m) = m := by
  have h := crtIdx_crtPinv hcop hpos (crtIdx_lt hpos m)
  exact crtIdx_inj hcop hpos (crtPinv_lt hcop hpos (crtIdx_lt hpos m)) hm h

/-! ## The label lists -/

theorem sigmaList_inj {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime)
    (hpos : ∀ s ∈ ss, 0 < s) {i j : ℕ} (hi : i < ss.prod) (hj : j < ss.prod)
    (h : (sigmaList ss).getD i 0 = (sigmaList ss).getD j 0) : i = j := by
  rw [sigmaList_getD hi, sigmaList_getD hj] at h
  exact crtIdx_inj hcop hpos hi hj h

theorem sigmaList_lt {ss : List ℕ} (hpos : ∀ s ∈ ss, 0 < s) {i : ℕ} (hi : i < ss.prod) :
    (sigmaList ss).getD i 0 < ss.prod := by
  rw [sigmaList_getD hi]; exact crtIdx_lt hpos i

theorem sigmaList_nodup {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime)
    (hpos : ∀ s ∈ ss, 0 < s) : (sigmaList ss).Nodup := by
  rw [sigmaList, List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_map, List.length_range] at hi hj
  simp only [List.getElem_map, List.getElem_range]
  intro h
  exact absurd (crtIdx_inj hcop hpos hi hj h) (Nat.ne_of_lt hij)

theorem crtQ_getD {ss : List ℕ} {j : ℕ} (hj : j < ss.prod) :
    (crtQ ss).getD j 0 = crtPinv ss j := by
  rw [List.getD_eq_getElem _ _ (by simpa [crtQ] using hj)]
  simp [crtQ]

theorem crtQ_inj {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {i j : ℕ} (hi : i < ss.prod) (hj : j < ss.prod)
    (h : (crtQ ss).getD i 0 = (crtQ ss).getD j 0) : i = j := by
  rw [crtQ_getD hi, crtQ_getD hj] at h
  rw [← crtIdx_crtPinv hcop hpos hi, ← crtIdx_crtPinv hcop hpos hj]
  rw [h]

theorem crtQ_lt {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {j : ℕ} (hj : j < ss.prod) : (crtQ ss).getD j 0 < ss.prod := by
  rw [crtQ_getD hj]; exact crtPinv_lt hcop hpos hj

theorem crtQ_nodup {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s) :
    (crtQ ss).Nodup := by
  rw [crtQ, List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_map, List.length_range] at hi hj
  simp only [List.getElem_map, List.getElem_range]
  intro h
  have h2 : crtIdx ss (crtPinv ss i) = crtIdx ss (crtPinv ss j) := by rw [h]
  rw [crtIdx_crtPinv hcop hpos hi, crtIdx_crtPinv hcop hpos hj] at h2
  exact absurd h2 (Nat.ne_of_lt hij)

/-! ## `invLab` for the two label lists -/

theorem invLab_sigmaList {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime)
    (hpos : ∀ s ∈ ss, 0 < s) {m : ℕ} (hm : m < ss.prod) :
    invLab (sigmaList ss) m = crtPinv ss m := by
  have hex : ∃ j, j < (sigmaList ss).length ∧ (sigmaList ss).getD j 0 = m :=
    ⟨crtPinv ss m, by simpa [sigmaList_length] using crtPinv_lt hcop hpos hm,
      by rw [sigmaList_getD (crtPinv_lt hcop hpos hm), crtIdx_crtPinv hcop hpos hm]⟩
  have h1 : invLab (sigmaList ss) m < ss.prod := by
    have := (invLab_spec hex).1
    simpa [sigmaList_length] using this
  have h2 : (sigmaList ss).getD (invLab (sigmaList ss) m) 0
      = (sigmaList ss).getD (crtPinv ss m) 0 := by
    rw [(invLab_spec hex).2, sigmaList_getD (crtPinv_lt hcop hpos hm), crtIdx_crtPinv hcop hpos hm]
  exact sigmaList_inj hcop hpos h1 (crtPinv_lt hcop hpos hm) h2

theorem invLab_crtQ {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s)
    {m : ℕ} (hm : m < ss.prod) : invLab (crtQ ss) m = crtIdx ss m := by
  have hex : ∃ j, j < (crtQ ss).length ∧ (crtQ ss).getD j 0 = m :=
    ⟨crtIdx ss m, by simpa [crtQ_length] using crtIdx_lt hpos m,
      by rw [crtQ_getD (crtIdx_lt hpos m), crtPinv_crtIdx hcop hpos hm]⟩
  have h1 : invLab (crtQ ss) m < ss.prod := by
    have := (invLab_spec hex).1
    simpa [crtQ_length] using this
  have h2 : (crtQ ss).getD (invLab (crtQ ss) m) 0 = (crtQ ss).getD (crtIdx ss m) 0 := by
    rw [(invLab_spec hex).2, crtQ_getD (crtIdx_lt hpos m), crtPinv_crtIdx hcop hpos hm]
  exact crtQ_inj hcop hpos h1 (crtIdx_lt hpos m) h2

end Work.MainP
