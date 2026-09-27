import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.bary_inj
import Submission.Work.PL.Shell.convexHull_inter_bary
import Submission.Work.PL.Shell.affineIndependent_bary_image
import Submission.Work.PL.Shell.flagEnum_mem
import Submission.Work.PL.Shell.flagEnum_sorted
import Submission.Work.PL.Shell.flagEnum_mem_take
import Submission.Work.PL.Shell.exists_flag_contains
import Submission.Work.PL.Subdiv.Coord

namespace Work.PL.Shell

open Set Metric Finset
open scoped BigOperators

noncomputable section

variable {N : ℕ}

/-! ### Elementary list facts about `prefAt` -/

theorem prefAt_mono {l : List (PL.E N)} {j k : ℕ} (hjk : j ≤ k) :
    prefAt l j ⊆ prefAt l k := by
  intro x hx
  rw [prefAt, List.mem_toFinset] at hx ⊢
  exact List.take_subset_take_left l (by omega : j + 1 ≤ k + 1) hx

theorem prefAt_card {l : List (PL.E N)} (hl : l.Nodup) {j : ℕ} (hj : j < l.length) :
    (prefAt l j).card = j + 1 := by
  have hnod : (l.take (j+1)).Nodup := List.Pairwise.sublist (List.take_sublist (j+1) l) hl
  rw [prefAt, List.toFinset_card_of_nodup hnod,
      List.length_take_of_le (by omega : j + 1 ≤ l.length)]

theorem prefAt_inj {l : List (PL.E N)} (hl : l.Nodup) {j k : ℕ}
    (hj : j < l.length) (hk : k < l.length)
    (h : prefAt l j = prefAt l k) : j = k := by
  have h1 := prefAt_card hl hj
  have h2 := prefAt_card hl hk
  rw [h] at h1
  omega

theorem prefAt_last {l : List (PL.E N)} (hl : l.Nodup) (hpos : 0 < l.length) :
    prefAt l (l.length - 1) = l.toFinset := by
  rw [prefAt, Nat.sub_add_cancel hpos, List.take_length]

theorem prefAt_subset_toFinset {l : List (PL.E N)} {j : ℕ} : prefAt l j ⊆ l.toFinset := by
  intro x hx
  rw [prefAt, List.mem_toFinset] at hx
  exact List.mem_toFinset.mpr (List.mem_of_mem_take hx)

theorem prefAt_nonempty {l : List (PL.E N)} (hl : l.Nodup) {j : ℕ} (hj : j < l.length) :
    (prefAt l j).Nonempty :=
  Finset.card_pos.mp (by rw [prefAt_card hl hj]; omega)

theorem getElem_mem_prefAt {l : List (PL.E N)} {j i : ℕ} (hi : i ≤ j) (hj : j < l.length) :
    l[i] ∈ prefAt l j := by
  rw [prefAt, List.mem_toFinset, List.mem_take_iff_getElem]
  exact ⟨i, by rw [Nat.min_eq_left (by omega : j + 1 ≤ l.length)]; omega, rfl⟩

theorem ft_prefAt_mem_prefixes {l : List (PL.E N)} {j : ℕ} (hj : j < l.length) :
    prefAt l j ∈ prefixes l :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

theorem prefixes_chain {l : List (PL.E N)} :
    ∀ A ∈ prefixes l, ∀ B ∈ prefixes l, A ⊆ B ∨ B ⊆ A := by
  intro A hA B hB
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hB
  rcases le_total j k with h | h
  · exact Or.inl (prefAt_mono h)
  · exact Or.inr (prefAt_mono h)

theorem ft_prefixes_subset_toFinset {l : List (PL.E N)} :
    ∀ A ∈ prefixes l, A ⊆ l.toFinset := by
  intro A hA
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hA
  exact prefAt_subset_toFinset

theorem ft_prefixes_nonempty {l : List (PL.E N)} (hl : l.Nodup) :
    ∀ A ∈ prefixes l, A.Nonempty := by
  intro A hA
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hA
  exact prefAt_nonempty hl (Finset.mem_range.mp hj)

theorem nodup_of_pairwise_map {vs : List (PL.E N)} {rk : PL.E N → ℕ}
    (hrk : (vs.map rk).Pairwise (· < ·)) : vs.Nodup := by
  have h1 : vs.Pairwise (fun a b => rk a < rk b) := List.pairwise_map.mp hrk
  exact h1.imp (fun {a b} h hab => by rw [hab] at h; exact absurd h (lt_irrefl (rk b)))

theorem perm_toFinset {l l' : List (PL.E N)} (h : l.Perm l') : l.toFinset = l'.toFinset := by
  ext x
  simp only [List.mem_toFinset]
  exact h.mem_iff

theorem rk_inj_on_of_pairwise {vs : List (PL.E N)} {rk : PL.E N → ℕ}
    (hrk : (vs.map rk).Pairwise (· < ·)) {l : List (PL.E N)} (hl : l.Perm vs) :
    ∀ x ∈ l, ∀ y ∈ l, rk x = rk y → x = y := by
  have hnd : (vs.map rk).Nodup := hrk.nodup
  have key : ∀ x ∈ vs, ∀ y ∈ vs, rk x = rk y → x = y := by
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.mp hy
    subst hjy
    have himg : i = j := by
      have h1 : (vs.map rk)[i]'(by simpa using hi) = (vs.map rk)[j]'(by simpa using hj) := by
        rw [List.getElem_map, List.getElem_map, hxy]
      exact hnd.getElem_inj_iff.mp h1
    subst himg
    rfl
  intro x hx y hy hxy
  exact key x (hl.mem_iff.mp hx) y (hl.mem_iff.mp hy) hxy

/-! ### Membership bookkeeping for `J.image (prefAt l)` -/

theorem image_prefAt_subset {l : List (PL.E N)} {J : Finset ℕ} {Δ : Finset (PL.E N)}
    (hJ : ∀ j ∈ J, j < l.length) (hlΔ : l.toFinset = Δ) :
    ∀ A ∈ J.image (prefAt l), A ⊆ Δ := by
  intro A hA
  obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hA
  rw [← hlΔ]
  exact prefAt_subset_toFinset

theorem image_prefAt_nonempty {l : List (PL.E N)} {J : Finset ℕ}
    (hl : l.Nodup) (hJ : ∀ j ∈ J, j < l.length) :
    ∀ A ∈ J.image (prefAt l), A.Nonempty := by
  intro A hA
  obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hA
  exact prefAt_nonempty hl (hJ j hjJ)

theorem image_prefAt_chain {l : List (PL.E N)} {J : Finset ℕ} :
    ∀ A ∈ J.image (prefAt l), ∀ B ∈ J.image (prefAt l), A ⊆ B ∨ B ⊆ A := by
  intro A hA B hB
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hB
  rcases le_total j k with h | h
  · exact Or.inl (prefAt_mono h)
  · exact Or.inr (prefAt_mono h)

/-! ### `keyLt` is a strict lexicographic order -/

theorem keyLt_irrefl {a : List ℕ} : ¬ keyLt a a := by
  rintro ⟨i, -, -, x, y, hx, hy, hlt⟩
  have hxy : x = y := Option.some.inj (hx.symm.trans hy)
  omega

theorem keyLt_asymm {a b : List ℕ} (hlen : a.length = b.length)
    (h : keyLt a b) (hba : keyLt b a) : False := by
  obtain ⟨i, hi, hti, x, y, hxi, hyi, hlt⟩ := h
  obtain ⟨j, hj, htj, x', y', hxj, hyj, hlt'⟩ := hba
  rcases lt_trichotomy i j with hij | heq | hji
  · have h1 : a[i]? = b[i]? := by
      rw [← List.getElem?_take_of_lt (l := a) hij, ← List.getElem?_take_of_lt (l := b) hij, htj]
    have hxy : x = y := Option.some.inj (hxi.symm.trans (h1.trans hyi))
    omega
  · subst heq
    have h1 : x = y' := Option.some.inj (hxi.symm.trans hyj)
    have h2 : y = x' := Option.some.inj (hyi.symm.trans hxj)
    omega
  · have h1 : a[j]? = b[j]? := by
      rw [← List.getElem?_take_of_lt (l := a) hji, ← List.getElem?_take_of_lt (l := b) hji, hti]
    have hxy : x' = y' := Option.some.inj (hxj.symm.trans (h1.symm.trans hyj))
    omega


/-! ### The two inclusion directions -/

/-- If `w ∈ T` is not in the prefix set `prefAt l (max J)`, then the whole small simplex
`σ_J` lies in the facet opposite `w`. -/
theorem subset_facet {Δ T : Finset (PL.E N)} {l : List (PL.E N)} {J : Finset ℕ}
    (hJne : J.Nonempty) (hJ : ∀ j ∈ J, j < l.length) (hlnod : l.Nodup) (hlΔ : l.toFinset = Δ)
    {w : PL.E N} (hwT : w ∈ T) (hwm : w ∉ prefAt l (J.max' hJne)) :
    PL.simp ((J.image (prefAt l)).image bary) ⊆ PL.simp (Δ.erase w) := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro x hx
  simp only [Finset.mem_coe] at hx
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hS
  have hjm : j ≤ J.max' hJne := J.le_max' j hjJ
  have hsub : prefAt l j ⊆ prefAt l (J.max' hJne) := prefAt_mono hjm
  have hwj : w ∉ prefAt l j := fun h => hwm (hsub h)
  have hne : (prefAt l j).Nonempty := prefAt_nonempty hlnod (hJ j hjJ)
  have hmem : bary (prefAt l j) ∈ PL.simp (prefAt l j) := Work.PL.Subdiv.bary_mem_simp hne
  have hsub2 : prefAt l j ⊆ Δ.erase w := by
    intro y hy
    rw [Finset.mem_erase]
    exact ⟨fun hyw => hwj (hyw ▸ hy), by rw [← hlΔ]; exact prefAt_subset_toFinset hy⟩
  exact convexHull_mono (Finset.coe_subset.mpr hsub2) hmem

/-- If `¬ ascIdx rk l ⊆ J`, then the whole small simplex `σ_J` lies in the union of the
top simplices of the strictly earlier flags. -/
theorem subset_earlier {vs : List (PL.E N)} {rk : PL.E N → ℕ}
    (hrk : (vs.map rk).Pairwise (· < ·)) {l : List (PL.E N)} (hl : l ∈ flagEnum vs)
    {J : Finset ℕ} (hJ : ∀ j ∈ J, j < l.length) (hQ : ¬ (ascIdx rk l ⊆ J)) :
    PL.simp ((J.image (prefAt l)).image bary) ⊆
      ⋃ j ∈ Finset.range ((flagEnum vs).idxOf l),
        PL.simp ((prefixes ((flagEnum vs).getD j [])).image bary) := by
  have hvs' : vs.Nodup := nodup_of_pairwise_map hrk
  obtain ⟨l', hl'take, hP⟩ := (exists_flag_contains hvs' hrk hl hJ).mpr hQ
  have hl'mem : l' ∈ flagEnum vs := List.mem_of_mem_take hl'take
  have hn : (flagEnum vs).idxOf l' < (flagEnum vs).idxOf l :=
    (List.mem_take_iff_idxOf_lt hl'mem).mp hl'take
  have h1 : PL.simp ((J.image (prefAt l)).image bary) ⊆ PL.simp ((prefixes l').image bary) := by
    apply convexHull_mono
    intro x hx
    simp only [Finset.mem_coe] at hx ⊢
    obtain ⟨S, hS, hxS⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hS
    rw [← hxS]
    exact Finset.mem_image.mpr ⟨prefAt l j, hP j hjJ, rfl⟩
  have hgd : (flagEnum vs).getD ((flagEnum vs).idxOf l') [] = l' := by
    rw [List.getD_eq_getElem (flagEnum vs) [] (List.idxOf_lt_length_iff.mpr hl'mem)]
    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hl'mem)
  intro x hx
  refine Set.mem_iUnion₂.mpr ⟨(flagEnum vs).idxOf l', Finset.mem_range.mpr hn, ?_⟩
  rw [hgd]
  exact h1 hx

/-- If all vertices of `T` lie in `prefAt l (max J)` while `ascIdx rk l ⊆ J`, then the
interior point of `σ_J` lies outside the union of the `T`-facets and of the earlier
top simplices. -/
theorem not_subset_of_not_rhs {Δ T : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    {vs : List (PL.E N)} {rk : PL.E N → ℕ} (hvs : vs.toFinset = Δ)
    (hrk : (vs.map rk).Pairwise (· < ·))
    {l : List (PL.E N)} (hl : l ∈ flagEnum vs) {J : Finset ℕ} (hJne : J.Nonempty)
    (hJ : ∀ j ∈ J, j < l.length) (hTΔ : T ⊆ Δ)
    (hTs : ∀ w ∈ T, w ∈ prefAt l (J.max' hJne)) (hasc : ascIdx rk l ⊆ J) :
    ¬ (PL.simp ((J.image (prefAt l)).image bary) ⊆
        (⋃ w ∈ T, PL.simp (Δ.erase w)) ∪
          ⋃ j ∈ Finset.range ((flagEnum vs).idxOf l),
            PL.simp ((prefixes ((flagEnum vs).getD j [])).image bary)) := by
  intro hsub
  have hvs' : vs.Nodup := nodup_of_pairwise_map hrk
  have hlperm : l.Perm vs := flagEnum_mem.mp hl
  have hlnod : l.Nodup := hlperm.nodup_iff.mpr hvs'
  have hlΔ : l.toFinset = Δ := by rw [perm_toFinset hlperm, hvs]
  set C : Finset (Finset (PL.E N)) := J.image (prefAt l) with hC
  set p : PL.E N := bary (C.image bary) with hp
  have hCne' : C.Nonempty := by rw [hC]; exact hJne.image _
  have hCsub : ∀ A ∈ C, A ⊆ Δ := by
    intro A hA; rw [hC] at hA; exact image_prefAt_subset hJ hlΔ A hA
  have hCne : ∀ A ∈ C, A.Nonempty := by
    intro A hA; rw [hC] at hA; exact image_prefAt_nonempty hlnod hJ A hA
  have hCchain : ∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A := by
    intro A hA B hB; rw [hC] at hA hB; exact image_prefAt_chain A hA B hB
  have hCboth : ∀ A ∈ C, A.Nonempty ∧ A ⊆ Δ := fun A hA => ⟨hCne A hA, hCsub A hA⟩
  have hinjC : Set.InjOn bary (↑C : Set (Finset (PL.E N))) := by
    intro A hA B hB hAB
    exact bary_inj hΔ (hCne A (by simpa using hA)) (hCne B (by simpa using hB))
      (hCsub A (by simpa using hA)) (hCsub B (by simpa using hB)) hAB
  have hcardV : (C.image bary).card = C.card := Finset.card_image_of_injOn hinjC
  have hVne : (C.image bary).Nonempty := by
    obtain ⟨A, hA⟩ := hCne'
    exact ⟨bary A, Finset.mem_image.mpr ⟨A, hA, rfl⟩⟩
  have hp_mem : p ∈ PL.simp (C.image bary) := by
    rw [hp]; exact Work.PL.Subdiv.bary_mem_simp hVne
  have hp_eq : p = ∑ ρ ∈ C, (C.card : ℝ)⁻¹ • bary ρ := by
    rw [hp]
    show ((C.image bary).card : ℝ)⁻¹ • ∑ x ∈ C.image bary, x
        = ∑ ρ ∈ C, (C.card : ℝ)⁻¹ • bary ρ
    rw [Finset.sum_image hinjC, hcardV, Finset.smul_sum]
  have hp_in : p ∈ (⋃ w ∈ T, PL.simp (Δ.erase w)) ∪
      ⋃ j ∈ Finset.range ((flagEnum vs).idxOf l),
        PL.simp ((prefixes ((flagEnum vs).getD j [])).image bary) := hsub hp_mem
  have hCnonneg : (0:ℝ) ≤ (C.card : ℝ) := Nat.cast_nonneg _
  have notMem_B : ∀ w ∈ T, p ∉ PL.simp (Δ.erase w) := by
    intro w hwT hpw
    set a : PL.E N → ℝ := fun v => ∑ ρ ∈ C.filter (fun ρ => v ∈ ρ), ((C.card : ℝ)⁻¹) / (ρ.card : ℝ)
      with ha
    have hCpos : (0:ℝ) < (C.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hCne'
    have ha0 : ∀ v ∈ Δ, 0 ≤ a v := by
      intro v _
      rw [ha]
      exact Finset.sum_nonneg (fun ρ _ => div_nonneg (inv_nonneg.mpr hCnonneg) (Nat.cast_nonneg _))
    have hasum : ∑ v ∈ Δ, a v = 1 := by
      rw [ha]
      rw [Work.PL.Subdiv.sum_coeff_filter C Δ hCsub hCne (fun _ => ((C.card : ℝ)⁻¹))]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [mul_comm, inv_mul_cancel₀ (ne_of_gt hCpos)]
    have hax : ∑ v ∈ Δ, a v • v = p := by
      rw [ha, hp_eq]
      exact (Work.PL.Subdiv.sum_smul_bary_eq_sum_smul C Δ hCsub
        (fun _ => ((C.card : ℝ)⁻¹))).symm
    have hρ0 : prefAt l (J.max' hJne) ∈ C.filter (fun ρ => w ∈ ρ) := by
      rw [Finset.mem_filter]
      refine ⟨?_, hTs w hwT⟩
      rw [hC]
      exact Finset.mem_image.mpr ⟨J.max' hJne, J.max'_mem hJne, rfl⟩
    have hterm : 0 < ((C.card : ℝ)⁻¹) / ((prefAt l (J.max' hJne)).card : ℝ) := by
      apply div_pos (inv_pos.mpr hCpos)
      exact_mod_cast Finset.card_pos.mpr (prefAt_nonempty hlnod (hJ _ (J.max'_mem hJne)))
    have hpos : 0 < a w := by
      rw [ha]
      beta_reduce
      exact lt_of_lt_of_le hterm
        (Finset.single_le_sum (fun ρ _ => div_nonneg (inv_nonneg.mpr hCnonneg) (Nat.cast_nonneg _)) hρ0)
    have hzero : a w = 0 :=
      (Work.PL.Subdiv.coords_eq_zero_of_mem_simp_subset (a := a) (Finset.erase_subset w Δ) hΔ
        ha0 hasum hax hpw) w (hTΔ hwT) (Finset.notMem_erase w Δ)
    linarith
  have notMem_E : ∀ j0, j0 < (flagEnum vs).idxOf l →
      p ∉ PL.simp ((prefixes ((flagEnum vs).getD j0 [])).image bary) := by
    intro j0 hj0 hpT
    have hidxle : (flagEnum vs).idxOf l < (flagEnum vs).length := List.idxOf_lt_length_iff.mpr hl
    have hj0len : j0 < (flagEnum vs).length := lt_trans hj0 hidxle
    set l' : List (PL.E N) := (flagEnum vs).getD j0 [] with hl'
    have hl'take : l' ∈ (flagEnum vs).take ((flagEnum vs).idxOf l) := by
      rw [hl', List.getD_eq_getElem (flagEnum vs) [] hj0len]
      refine List.mem_take_iff_getElem.mpr ⟨j0, ?_, rfl⟩
      rw [Nat.min_eq_left (le_of_lt hidxle)]
      exact hj0
    have hl'mem : l' ∈ flagEnum vs := List.mem_of_mem_take hl'take
    have hl'perm : l'.Perm vs := flagEnum_mem.mp hl'mem
    have hl'nod : l'.Nodup := hl'perm.nodup_iff.mpr hvs'
    have hl'Δ : l'.toFinset = Δ := by rw [perm_toFinset hl'perm, hvs]
    have hcontra : ¬ (∃ l2 ∈ (flagEnum vs).take ((flagEnum vs).idxOf l),
        ∀ j ∈ J, prefAt l j ∈ prefixes l2) :=
      fun hA => (exists_flag_contains hvs' hrk hl hJ).mp hA hasc
    have hwit : ∃ j, j ∈ J ∧ prefAt l j ∉ prefixes l' := by
      by_contra hcon
      push_neg at hcon
      exact hcontra ⟨l', hl'take, fun j hj => hcon j hj⟩
    obtain ⟨j1, hj1J, hj1not⟩ := hwit
    have hC'sub : ∀ A ∈ prefixes l', A ⊆ Δ := by
      intro A hA; rw [← hl'Δ]; exact ft_prefixes_subset_toFinset A hA
    have hC'ne : ∀ A ∈ prefixes l', A.Nonempty := ft_prefixes_nonempty hl'nod
    have hC'both : ∀ A ∈ prefixes l', A.Nonempty ∧ A ⊆ Δ :=
      fun A hA => ⟨hC'ne A hA, hC'sub A hA⟩
    have hchain' : ∀ A ∈ prefixes l', ∀ B ∈ prefixes l', A ⊆ B ∨ B ⊆ A := prefixes_chain
    have hpT' : p ∈ PL.simp ((prefixes l').image bary) := hpT
    have hinter : p ∈ PL.simp ((C ∩ prefixes l').image bary) := by
      have h := Work.PL.Shell.convexHull_inter_bary hΔ hCboth hC'both hCchain hchain'
      rw [← h]
      exact ⟨hp_mem, hpT'⟩
    have hinjV : AffineIndependent ℝ ((↑) : ↥(C.image bary) → PL.E N) :=
      affineIndependent_bary_image hΔ hCboth hCchain
    set w1 : PL.E N → ℝ :=
      fun x => if x ∈ C.image bary then ((C.image bary).card : ℝ)⁻¹ else 0 with hw1
    have hw1sum : ∑ x ∈ C.image bary, w1 x = 1 := by
      rw [hw1, Finset.sum_congr rfl (fun x hx => if_pos hx)]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [mul_comm, inv_mul_cancel₀ (by exact_mod_cast Finset.card_ne_zero.mpr hVne)]
    have hw1pt : ∑ x ∈ C.image bary, w1 x • x = p := by
      rw [hw1, hp]
      show ∑ x ∈ C.image bary,
          (if x ∈ C.image bary then ((C.image bary).card : ℝ)⁻¹ else 0) • x
        = ((C.image bary).card : ℝ)⁻¹ • ∑ x ∈ C.image bary, x
      rw [Finset.sum_congr rfl (fun x hx => by rw [if_pos hx]), Finset.smul_sum]
    have hw1nonneg : ∀ v ∈ C.image bary, 0 ≤ w1 v := by
      intro v _
      show 0 ≤ (if v ∈ C.image bary then ((C.image bary).card : ℝ)⁻¹ else 0)
      by_cases hv : v ∈ C.image bary
      · rw [if_pos hv]; exact inv_nonneg.mpr (Nat.cast_nonneg _)
      · rw [if_neg hv]
    have hsubB' : ((C ∩ prefixes l').image bary) ⊆ (C.image bary) := by
      intro x hx
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨S, (Finset.mem_inter.mp hS).1, rfl⟩
    have hb1V : bary (prefAt l j1) ∈ C.image bary := by
      rw [hC]
      exact Finset.mem_image.mpr ⟨prefAt l j1, Finset.mem_image.mpr ⟨j1, hj1J, rfl⟩, rfl⟩
    have hb1not : bary (prefAt l j1) ∉ (C ∩ prefixes l').image bary := by
      intro hcon
      obtain ⟨S, hS, hSb⟩ := Finset.mem_image.mp hcon
      have hSC : S ∈ C := (Finset.mem_inter.mp hS).1
      have hSP : S ∈ prefixes l' := (Finset.mem_inter.mp hS).2
      obtain ⟨j2, _, hj2eq⟩ := by rw [hC] at hSC; exact Finset.mem_image.mp hSC
      have heq : S = prefAt l j1 :=
        bary_inj hΔ (hCne S hSC)
          (hCne (prefAt l j1) (by rw [hC]; exact Finset.mem_image.mpr ⟨j1, hj1J, rfl⟩))
          (hCsub S hSC) (hCsub (prefAt l j1) (by rw [hC]; exact Finset.mem_image.mpr ⟨j1, hj1J, rfl⟩)) hSb
      exact hj1not (heq ▸ hSP)
    have hz := Work.PL.Subdiv.coords_eq_zero_of_mem_simp_subset (a := w1) hsubB' hinjV
      hw1nonneg hw1sum hw1pt hinter
    have hzw : (if bary (prefAt l j1) ∈ C.image bary
        then ((C.image bary).card : ℝ)⁻¹ else 0) = 0 :=
      hz (bary (prefAt l j1)) hb1V hb1not
    rw [if_pos hb1V] at hzw
    have hposV : (0:ℝ) < ((C.image bary).card : ℝ)⁻¹ := by
      rw [inv_pos]; exact_mod_cast Finset.card_pos.mpr hVne
    linarith
  rcases Set.mem_or_mem_of_mem_union hp_in with hpB | hpE
  · obtain ⟨w, hwT, hpw⟩ := Set.mem_iUnion₂.mp hpB
    exact notMem_B w hwT hpw
  · obtain ⟨j0, hj0r, hpT⟩ := Set.mem_iUnion₂.mp hpE
    exact notMem_E j0 (Finset.mem_range.mp hj0r) hpT

/-- **Statement of the delegated lemma.** -/
theorem face_trace {N : ℕ} {Δ T : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    (vs : List (PL.E N)) (rk : PL.E N → ℕ)
    (hvs : vs.toFinset = Δ) (hrk : (vs.map rk).Pairwise (· < ·))
    (hT₁ : T.Nonempty) (hT₂ : T ⊂ Δ)
    (hT : ∀ u ∈ T, ∀ w ∈ Δ, w ∉ T → rk u < rk w)
    {l : List (PL.E N)} (hl : l ∈ Work.PL.Shell.flagEnum vs) {J : Finset ℕ} (hJne : J.Nonempty)
    (hJ : ∀ j ∈ J, j < l.length) :
    PL.simp ((J.image (Work.PL.Shell.prefAt l)).image Work.PL.Shell.bary) ⊆
        (⋃ w ∈ T, PL.simp (Δ.erase w)) ∪
          ⋃ j ∈ Finset.range ((Work.PL.Shell.flagEnum vs).idxOf l),
            PL.simp ((Work.PL.Shell.prefixes ((Work.PL.Shell.flagEnum vs).getD j [])).image
              Work.PL.Shell.bary)
      ↔ (∃ w ∈ T, w ∉ Work.PL.Shell.prefAt l (J.max' hJne)) ∨
          ¬ (Work.PL.Shell.ascIdx rk l ⊆ J) := by
  have hvs' : vs.Nodup := nodup_of_pairwise_map hrk
  have hlperm : l.Perm vs := flagEnum_mem.mp hl
  have hlnod : l.Nodup := hlperm.nodup_iff.mpr hvs'
  have hlΔ : l.toFinset = Δ := by rw [perm_toFinset hlperm, hvs]
  have hTΔ : T ⊆ Δ := hT₂.1
  constructor
  · intro hsub
    by_contra h
    push_neg at h
    exact not_subset_of_not_rhs hΔ hvs hrk hl hJne hJ hTΔ h.1 h.2 hsub
  · rintro (⟨w, hwT, hw⟩ | hQ)
    · refine (subset_facet hJne hJ hlnod hlΔ hwT hw).trans ?_
      intro x hx
      exact Set.mem_union_left _ (Set.mem_iUnion₂.mpr ⟨w, hwT, hx⟩)
    · refine (subset_earlier hrk hl hJ hQ).trans ?_
      intro x hx
      exact Set.mem_union_right _ hx

end

end Work.PL.Shell
