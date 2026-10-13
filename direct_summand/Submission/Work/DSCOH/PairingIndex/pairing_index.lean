import Mathlib
import Submission.Work.DSCOH.Norm.FirstHomDefs
import Submission.Work.DSCOH.Norm.sign_sort_succAbove
import Submission.Work.DSCOH.Norm.ReadFib.readAFiber

namespace Work.DSCOH.PairingIndex

open Work.DSCOH.Norm

set_option maxHeartbeats 1600000

/-! ## Elementary API for `Fin.succAbove` values -/

lemma succAbove_val {N : ℕ} (p : Fin (N+1)) (a : Fin N) :
    ((p.succAbove a : Fin (N+1)) : ℕ) = if (a:ℕ) < (p:ℕ) then (a:ℕ) else (a:ℕ) + 1 := by
  by_cases h : (a:ℕ) < (p:ℕ)
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h), ite_eq_left h]
    simp
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp only [Fin.le_def, Fin.val_castSucc]; omega),
      ite_eq_right h]
    simp

lemma succAbove_val_of_lt {k : ℕ} {m : Fin (k+2)} {a : Fin (k+1)}
    (h : m < Fin.succAbove m a) : ((Fin.succAbove m a : Fin (k+2)) : ℕ) = (a:ℕ) + 1 := by
  by_cases h' : (a:ℕ) < (m:ℕ)
  · exfalso
    have hv : ((Fin.succAbove m a : Fin (k+2)) : ℕ) = (a:ℕ) := by
      rw [succAbove_val]; exact if_pos h'
    have := Fin.lt_def.mp h
    omega
  · rw [succAbove_val]; exact if_neg h'

lemma succAbove_val_of_gt {k : ℕ} {m : Fin (k+2)} {a : Fin (k+1)}
    (h : Fin.succAbove m a < m) : ((Fin.succAbove m a : Fin (k+2)) : ℕ) = (a:ℕ) := by
  by_cases h' : (a:ℕ) < (m:ℕ)
  · rw [succAbove_val]; exact if_pos h'
  · exfalso
    have hv : ((Fin.succAbove m a : Fin (k+2)) : ℕ) = (a:ℕ)+1 := by
      rw [succAbove_val]; exact if_neg h'
    have := Fin.lt_def.mp h
    omega

lemma succAbove_val_lt_self {N : ℕ} (p : Fin (N+1)) (a : Fin N) :
    ((p.succAbove a : Fin (N+1)) : ℕ) < (p:ℕ) ↔ (a:ℕ) < (p:ℕ) := by
  rw [succAbove_val]
  by_cases h : (a:ℕ) < (p:ℕ)
  · rw [if_pos h]
  · rw [if_neg h]
    constructor <;> intro hh <;> omega

/-! ## Counting lemmas -/

lemma card_filter_lt_nat_lt_iff {n : ℕ} (S : Finset (Fin n)) {u : Fin n} {c : ℕ} (hu : u ∈ S) :
    (S.filter (fun w => w.val < u.val)).card < (S.filter (fun w => w.val < c)).card ↔ u.val < c := by
  constructor
  · intro hlt
    by_contra hcon
    have hsub : S.filter (fun w => w.val < c) ⊆ S.filter (fun w => w.val < u.val) := by
      intro w hw
      rw [Finset.mem_filter] at hw ⊢
      exact ⟨hw.1, lt_of_lt_of_le hw.2 (not_lt.mp hcon)⟩
    have := Finset.card_le_card hsub
    omega
  · intro huc
    have hsub : S.filter (fun w => w.val < u.val) ⊆ S.filter (fun w => w.val < c) := by
      intro w hw
      rw [Finset.mem_filter] at hw ⊢
      exact ⟨hw.1, lt_trans hw.2 huc⟩
    have hmem : u ∈ S.filter (fun w => w.val < c) := Finset.mem_filter.mpr ⟨hu, huc⟩
    have hnotmem : u ∉ S.filter (fun w => w.val < u.val) := by
      rw [Finset.mem_filter]; exact fun h => lt_irrefl u h.2
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub, fun heq => hnotmem (heq ▸ hmem)⟩)

lemma filter_lt_image_of_strictMono {α β : Type*} [LinearOrder α] [LinearOrder β] [DecidableEq β]
    {e : α → β} (he : StrictMono e) (s : Finset α) (x : α) :
    (s.image e).filter (fun v => v < e x) = (s.filter (fun w => w < x)).image e := by
  rw [Finset.filter_image]
  congr 1
  exact Finset.filter_congr (fun w _ => he.lt_iff_lt)

/-! ## The sorting permutation commutes with `succAbove` -/

lemma sort_succAbove_apply {ι : Type*} [LinearOrder ι] {k : ℕ} (x : Fin (k+2) → ι)
    (c : Fin (k+2)) (i : Fin (k+1)) :
    Tuple.sort x (Fin.succAbove ((Tuple.sort x).symm c) i)
      = Fin.succAbove c (Tuple.sort (Work.DSCOH.Norm.del x c) i) := by
  have hdel : Work.DSCOH.Norm.del x c = x ∘ Fin.succAbove c := rfl
  have h := congrFun (Work.DSCOH.Norm.sort_comp_succAbove x c) i
  simp only [Function.comp_apply] at h
  rw [← hdel] at h
  exact h

/-! ## The head of the read after deleting an entry -/

lemma compl_headVal_lt {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ}
    (x : Fin (k+2) → ι) (c : Fin (k+2)) (a : Fin (k+1))
    (hca : (Tuple.sort x).symm c < Fin.succAbove ((Tuple.sort x).symm c) a) :
    (headVal x (Fin.succAbove ((Tuple.sort x).symm c) a))ᶜ
      = ((headVal (Work.DSCOH.Norm.del x c) a)ᶜ).image (Fin.succAbove c) := by
  classical
  ext z
  rw [Finset.mem_compl, Finset.mem_image]
  constructor
  · intro hz
    have hzc : z ≠ c := by
      intro hzc'
      apply hz
      rw [Work.DSCOH.Norm.ReadFib.mem_headVal_iff]
      exact ⟨(Tuple.sort x).symm c, Fin.lt_def.mp hca,
        by rw [Equiv.apply_symm_apply]; exact hzc'.symm⟩
    obtain ⟨v, hv⟩ := Fin.exists_succAbove_eq hzc
    refine ⟨v, ?_, hv⟩
    rw [Finset.mem_compl]
    intro hvH
    rw [Work.DSCOH.Norm.ReadFib.mem_headVal_iff] at hvH
    obtain ⟨i, hi, hiv⟩ := hvH
    apply hz
    rw [Work.DSCOH.Norm.ReadFib.mem_headVal_iff]
    refine ⟨Fin.succAbove ((Tuple.sort x).symm c) i, ?_, ?_⟩
    · exact Fin.lt_def.mp ((Fin.succAbove_lt_succAbove_iff).mpr (Fin.lt_def.mpr hi))
    · rw [sort_succAbove_apply, hiv]; exact hv
  · rintro ⟨v, hv, hvz⟩
    rw [Finset.mem_compl] at hv
    intro hz
    rw [Work.DSCOH.Norm.ReadFib.mem_headVal_iff] at hz
    obtain ⟨j, hj, hjz⟩ := hz
    by_cases hjm : j = (Tuple.sort x).symm c
    · rw [hjm] at hjz
      rw [Equiv.apply_symm_apply] at hjz
      exact Fin.succAbove_ne c v (hvz.trans hjz.symm)
    · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hjm
      apply hv
      rw [Work.DSCOH.Norm.ReadFib.mem_headVal_iff]
      refine ⟨i, ?_, ?_⟩
      · have hlt : Fin.succAbove ((Tuple.sort x).symm c) i
            < Fin.succAbove ((Tuple.sort x).symm c) a := by
          rw [hi]; exact Fin.lt_def.mpr hj
        exact Fin.lt_def.mp ((Fin.succAbove_lt_succAbove_iff).mp hlt)
      · rw [← hi] at hjz
        rw [sort_succAbove_apply] at hjz
        exact Fin.succAbove_right_injective (by rw [hjz, hvz])

lemma compl_headVal_gt {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ}
    (x : Fin (k+2) → ι) (c : Fin (k+2)) (a : Fin (k+1))
    (hca : Fin.succAbove ((Tuple.sort x).symm c) a < (Tuple.sort x).symm c) :
    (headVal x (Fin.succAbove ((Tuple.sort x).symm c) a))ᶜ
      = insert c (((headVal (Work.DSCOH.Norm.del x c) a)ᶜ).image (Fin.succAbove c)) := by
  classical
  ext z
  rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_image]
  constructor
  · intro hz
    by_cases hzc : z = c
    · exact Or.inl hzc
    · right
      obtain ⟨v, hv⟩ := Fin.exists_succAbove_eq hzc
      refine ⟨v, ?_, hv⟩
      rw [Finset.mem_compl]
      intro hvH
      rw [Work.DSCOH.Norm.ReadFib.mem_headVal_iff] at hvH
      obtain ⟨i, hi, hiv⟩ := hvH
      apply hz
      rw [Work.DSCOH.Norm.ReadFib.mem_headVal_iff]
      refine ⟨Fin.succAbove ((Tuple.sort x).symm c) i, ?_, ?_⟩
      · exact Fin.lt_def.mp ((Fin.succAbove_lt_succAbove_iff).mpr (Fin.lt_def.mpr hi))
      · rw [sort_succAbove_apply, hiv]; exact hv
  · rintro (hzc | ⟨v, hv, hvz⟩)
    · intro hc
      rw [hzc] at hc
      rw [Work.DSCOH.Norm.ReadFib.mem_headVal_iff] at hc
      obtain ⟨j, hj, hjz⟩ := hc
      have hjm : j = (Tuple.sort x).symm c :=
        (Tuple.sort x).injective (hjz.trans (Equiv.apply_symm_apply (Tuple.sort x) c).symm)
      rw [hjm] at hj
      have h1 := Fin.lt_def.mp hca
      have h2 := Fin.lt_def.mp hj
      omega
    · rw [Finset.mem_compl] at hv
      intro hz
      rw [Work.DSCOH.Norm.ReadFib.mem_headVal_iff] at hz
      obtain ⟨j, hj, hjz⟩ := hz
      by_cases hjm : j = (Tuple.sort x).symm c
      · rw [hjm] at hjz
        rw [Equiv.apply_symm_apply] at hjz
        exact Fin.succAbove_ne c v (hvz.trans hjz.symm)
      · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hjm
        apply hv
        rw [Work.DSCOH.Norm.ReadFib.mem_headVal_iff]
        refine ⟨i, ?_, ?_⟩
        · have hlt : Fin.succAbove ((Tuple.sort x).symm c) i
              < Fin.succAbove ((Tuple.sort x).symm c) a := by
            rw [hi]; exact Fin.lt_def.mpr hj
          exact Fin.lt_def.mp ((Fin.succAbove_lt_succAbove_iff).mp hlt)
        · rw [← hi] at hjz
          rw [sort_succAbove_apply] at hjz
          exact Fin.succAbove_right_injective (by rw [hjz, hvz])

/-! ## The tail embedding after deleting an entry -/

lemma tailEmb_compl_of_lt {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ}
    (x : Fin (k+2) → ι) (c : Fin (k+2)) (a : Fin (k+1))
    (hca : (Tuple.sort x).symm c < Fin.succAbove ((Tuple.sort x).symm c) a)
    (hva : ((Fin.succAbove ((Tuple.sort x).symm c) a : Fin (k+2)) : ℕ) = (a:ℕ) + 1)
    (i : Fin ((k+1) - (a:ℕ))) :
    tailEmb x (Fin.succAbove ((Tuple.sort x).symm c) a) ⟨(i:ℕ), by omega⟩
      = Fin.succAbove c (tailEmb (Work.DSCOH.Norm.del x c) a i) := by
  classical
  have hAB := compl_headVal_lt x c a hca
  conv_lhs => rw [Work.DSCOH.Norm.tailEmb]
  rw [Work.DSCOH.Norm.ReadFib.orderEmbOfFin_apply_eq_iff]
  constructor
  · rw [hAB]
    exact Finset.mem_image.mpr ⟨_,
      Finset.mem_compl.mpr (Work.DSCOH.Norm.tailEmb_mem (Work.DSCOH.Norm.del x c) a i), rfl⟩
  · rw [hAB]
    have hcard : (((headVal (Work.DSCOH.Norm.del x c) a)ᶜ).image (Fin.succAbove c)).filter
          (fun v => v < Fin.succAbove c (Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a i))
        = (((headVal (Work.DSCOH.Norm.del x c) a)ᶜ).filter
            (fun w => w < Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a i)).image
              (Fin.succAbove c) :=
      filter_lt_image_of_strictMono (Fin.strictMono_succAbove c) _ _
    rw [hcard, Finset.card_image_of_injective _ (Fin.succAbove_right_injective (p := c))]
    exact ((Work.DSCOH.Norm.ReadFib.tailEmb_eq_iff (Work.DSCOH.Norm.del x c) a i _).mp rfl).2

lemma tailEmb_compl_of_gt {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ}
    (x : Fin (k+2) → ι) (c : Fin (k+2)) (a : Fin (k+1))
    (hca : Fin.succAbove ((Tuple.sort x).symm c) a < (Tuple.sort x).symm c)
    (hva : ((Fin.succAbove ((Tuple.sort x).symm c) a : Fin (k+2)) : ℕ) = (a:ℕ))
    (j : Fin ((k+2) - ((Fin.succAbove ((Tuple.sort x).symm c) a : Fin (k+2)) : ℕ)))
    (hju : (j:ℕ) = (((headVal x (Fin.succAbove ((Tuple.sort x).symm c) a))ᶜ).filter
        (fun v => v < c)).card)
    (i : Fin ((k+1) - (a:ℕ)))
    (l : Fin ((k+2) - ((Fin.succAbove ((Tuple.sort x).symm c) a : Fin (k+2)) : ℕ)))
    (hl : (l:ℕ) = (i:ℕ) + (if (i:ℕ) < (j:ℕ) then 0 else 1)) :
    tailEmb x (Fin.succAbove ((Tuple.sort x).symm c) a) l
      = Fin.succAbove c (tailEmb (Work.DSCOH.Norm.del x c) a i) := by
  classical
  set S : Finset (Fin (k+1)) := headVal (Work.DSCOH.Norm.del x c) a with hS
  set u : Fin (k+1) := tailEmb (Work.DSCOH.Norm.del x c) a i with hu
  set B : Finset (Fin (k+2)) := Sᶜ.image (Fin.succAbove c) with hB
  have hAB : (headVal x (Fin.succAbove ((Tuple.sort x).symm c) a))ᶜ = insert c B :=
    compl_headVal_gt x c a hca
  have hcB : c ∉ B := by
    rw [hB]
    exact fun h => let ⟨w, _, hw⟩ := Finset.mem_image.mp h; Fin.succAbove_ne c w hw
  have huS : u ∈ Sᶜ := by
    rw [hu, hS]
    exact Finset.mem_compl.mpr (Work.DSCOH.Norm.tailEmb_mem (Work.DSCOH.Norm.del x c) a i)
  have hi_val : (i:ℕ) = ((Sᶜ).filter (fun w => w < u)).card := by
    rw [hu, hS]
    exact ((Work.DSCOH.Norm.ReadFib.tailEmb_eq_iff (Work.DSCOH.Norm.del x c) a i u).mp rfl).2
  rw [hAB] at hju
  have e2 : ((insert c B).filter (fun v => v < c)).card = (B.filter (fun v => v < c)).card := by
    rw [Finset.filter_insert, if_neg (lt_irrefl c)]
  have e3a : (B.filter (fun v => v < c)).card
      = ((Sᶜ).filter (fun w => (Fin.succAbove c w).val < c.val)).card := by
    rw [hB, Finset.filter_image,
      Finset.card_image_of_injective _ (Fin.succAbove_right_injective (p := c))]
    exact congrArg Finset.card (Finset.filter_congr (fun w _ => Fin.lt_def))
  have e3b : ((Sᶜ).filter (fun w => (Fin.succAbove c w).val < c.val)).card
      = ((Sᶜ).filter (fun w => w.val < c.val)).card :=
    congrArg Finset.card (Finset.filter_congr (fun w _ => succAbove_val_lt_self c w))
  have hjval : (j:ℕ) = ((Sᶜ).filter (fun w => w.val < c.val)).card := by
    rw [hju, e2, e3a, e3b]
  have hi' : (i:ℕ) = ((Sᶜ).filter (fun w => w.val < u.val)).card := by
    rw [hi_val, Finset.filter_congr (fun w _ => Fin.lt_def)]
  have hcsc : c < Fin.succAbove c u ↔ ¬ (u.val < c.val) := by
    rw [Fin.lt_def, succAbove_val]
    by_cases h : u.val < c.val
    · rw [if_pos h]
      constructor <;> intro hh <;> omega
    · rw [if_neg h]
      constructor <;> intro hh <;> omega
  have hkey : (i:ℕ) < (j:ℕ) ↔ ¬ (c < Fin.succAbove c u) := by
    rw [hi', hjval, card_filter_lt_nat_lt_iff (Sᶜ) huS]
    exact (hcsc.not.trans not_not).symm
  have hBcard : (B.filter (fun v => v < Fin.succAbove c u)).card = i.val := by
    rw [hB, filter_lt_image_of_strictMono (Fin.strictMono_succAbove c) _ _,
      Finset.card_image_of_injective _ (Fin.succAbove_right_injective (p := c))]
    exact hi_val.symm
  have hcard : ((insert c B).filter (fun v => v < Fin.succAbove c u)).card
      = i.val + (if c < Fin.succAbove c u then 1 else 0) := by
    rw [Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (fun hmem => hcB (Finset.mem_filter.mp hmem).1), hBcard]
    · rw [hBcard]; omega
  conv_lhs => rw [Work.DSCOH.Norm.tailEmb]
  rw [Work.DSCOH.Norm.ReadFib.orderEmbOfFin_apply_eq_iff]
  constructor
  · rw [hAB]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨u, huS, rfl⟩))
  · rw [hAB, hl, hcard]
    by_cases hij : (i:ℕ) < (j:ℕ)
    · rw [if_pos hij, if_neg (hkey.mp hij)]
    · rw [if_neg hij, if_pos (not_not.mp (hkey.not.mp hij))]

theorem pairing_index {ι : Type*} [LinearOrder ι] [Fintype ι] {k : ℕ} (x : Fin (k+2) → ι)
    (c : Fin (k+2)) (a : Fin (k+1)) (b : Fin (k+3))
    (hb : Work.DSCOH.Norm.readA x (Fin.succAbove ((Tuple.sort x).symm c) a) b = c) :
    (Fin.succAbove c) ∘ Work.DSCOH.Norm.readA (Work.DSCOH.Norm.del x c) a =
      Work.DSCOH.Norm.readA x (Fin.succAbove ((Tuple.sort x).symm c) a) ∘ (Fin.succAbove b) := by
  classical
  funext q
  simp only [Function.comp_apply]
  set m : Fin (k+2) := (Tuple.sort x).symm c with hm
  set a' : Fin (k+2) := Fin.succAbove m a with ha'
  have hb' : Work.DSCOH.Norm.readA x a' b = c := hb
  by_cases hble : (b:ℕ) ≤ (a':ℕ)
  · have h1 : Tuple.sort x ⟨(b:ℕ), by have := b.isLt; have := a'.isLt; omega⟩ = c := by
      have h := hb'
      rw [Work.DSCOH.Norm.readA_head x a' (p := b) hble] at h
      exact h
    have h2 : (⟨(b:ℕ), by have := b.isLt; have := a'.isLt; omega⟩ : Fin (k+2)) = m :=
      (Tuple.sort x).injective (h1.trans (by rw [hm, Equiv.apply_symm_apply]))
    have hbm_val : (b:ℕ) = (m:ℕ) := congrArg Fin.val h2
    rcases lt_or_eq_of_le hble with hba | hba
    · -- Case A: b < a'
      have hma' : m < a' := Fin.lt_def.mpr (by rw [← hbm_val]; exact hba)
      have hva : (a':ℕ) = (a:ℕ) + 1 := by
        rw [ha']; exact succAbove_val_of_lt hma'
      have hca_lt : (Tuple.sort x).symm c < Fin.succAbove ((Tuple.sort x).symm c) a := hma'
      by_cases hq_le : (q:ℕ) ≤ (a:ℕ)
      · -- Case A.a
        have hrq : Work.DSCOH.Norm.readA (Work.DSCOH.Norm.del x c) a q
            = Tuple.sort (Work.DSCOH.Norm.del x c) ⟨(q:ℕ), by have := q.isLt; omega⟩ :=
          Work.DSCOH.Norm.readA_head _ _ hq_le
        have hsb_val : ((Fin.succAbove b q : Fin (k+3)) : ℕ)
            = ((Fin.succAbove m ⟨(q:ℕ), by have := q.isLt; omega⟩ : Fin (k+2)) : ℕ) := by
          rw [succAbove_val, succAbove_val]
          simp only [Fin.val_mk]
          rw [hbm_val]
        have hle : ((Fin.succAbove b q : Fin (k+3)) : ℕ) ≤ (a':ℕ) := by
          rw [hsb_val, ha']
          exact Fin.le_def.mp ((Fin.strictMono_succAbove m).monotone (Fin.le_def.mpr hq_le))
        have hR : Work.DSCOH.Norm.readA x a' (Fin.succAbove b q)
            = Tuple.sort x (Fin.succAbove m (⟨(q:ℕ), by have := q.isLt; omega⟩ : Fin (k+1))) := by
          rw [Work.DSCOH.Norm.readA_head x a' (p := Fin.succAbove b q) hle]
          congr 1
          apply Fin.ext
          simp only [Fin.val_mk]
          exact hsb_val
        rw [hrq, hR, sort_succAbove_apply]
      · -- Case A.b
        have hq_gt : (a:ℕ) < (q:ℕ) := lt_of_not_ge hq_le
        have hrq : Work.DSCOH.Norm.readA (Work.DSCOH.Norm.del x c) a q
            = Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a
                ⟨(q:ℕ)-1-(a:ℕ), by have := q.isLt; omega⟩ :=
          Work.DSCOH.Norm.readA_tail _ _ hq_le
        have hsv : Fin.succAbove b q = (⟨(q:ℕ)+1, by have := q.isLt; omega⟩ : Fin (k+3)) := by
          apply Fin.ext
          rw [succAbove_val]
          rw [if_neg (by omega)]
        rw [hrq, hsv]
        rw [Work.DSCOH.Norm.readA_tail x a' (p := ⟨(q:ℕ)+1, by have := q.isLt; omega⟩)
          (by show ¬ ((q:ℕ)+1 ≤ (a':ℕ)); omega)]
        rw [← tailEmb_compl_of_lt x c a hca_lt hva ⟨(q:ℕ)-1-(a:ℕ), by have := q.isLt; omega⟩]
        congr 1
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
    · -- impossible: b and a' have equal values
      exfalso
      have h3 : m = a' := Fin.ext (by rw [← h2]; exact hba)
      exact Fin.succAbove_ne m a (by rw [ha'] at h3; exact h3.symm)
  · -- Case B: a' < b
    have hbagt : (a':ℕ) < (b:ℕ) := lt_of_not_ge hble
    have hbk : Work.DSCOH.Norm.tailEmb x a'
        ⟨(b:ℕ)-1-(a':ℕ), by have := b.isLt; have := a'.isLt; omega⟩ = c := by
      have h := hb'
      rw [Work.DSCOH.Norm.readA_tail x a' (p := b) (by show ¬ ((b:ℕ) ≤ (a':ℕ)); omega)] at h
      exact h
    have hcH : c ∉ headVal x a' := by
      intro hcon
      exact Work.DSCOH.Norm.tailEmb_mem x a' _ (by rw [hbk]; exact hcon)
    have hma' : a' < m := by
      have h1 : ¬ (m.val < (a':ℕ)) := by
        rw [Work.DSCOH.Norm.ReadFib.mem_headVal_iff] at hcH
        intro hlt
        exact hcH ⟨m, hlt, by rw [hm, Equiv.apply_symm_apply]⟩
      exact lt_of_le_of_ne (Fin.le_def.mpr (by omega))
        (by rw [ha']; exact Fin.succAbove_ne m a)
    have hva : (a':ℕ) = (a:ℕ) := by
      rw [ha']; exact succAbove_val_of_gt (by rw [ha'] at hma'; exact hma')
    have hca_gt : Fin.succAbove ((Tuple.sort x).symm c) a < (Tuple.sort x).symm c := hma'
    set j : Fin ((k+2) - (a':ℕ)) :=
      ⟨(b:ℕ)-1-(a':ℕ), by have := b.isLt; have := a'.isLt; omega⟩ with hj
    have hju : (j:ℕ) = (((headVal x a')ᶜ).filter (fun v => v < c)).card :=
      ((Work.DSCOH.Norm.ReadFib.tailEmb_eq_iff x a' j c).mp hbk).2
    by_cases hq_le : (q:ℕ) ≤ (a:ℕ)
    · -- Case B.a
      have hrq : Work.DSCOH.Norm.readA (Work.DSCOH.Norm.del x c) a q
          = Tuple.sort (Work.DSCOH.Norm.del x c) ⟨(q:ℕ), by have := q.isLt; omega⟩ :=
        Work.DSCOH.Norm.readA_head _ _ hq_le
      have hsv : Fin.succAbove b q = (⟨(q:ℕ), by have := q.isLt; omega⟩ : Fin (k+3)) := by
        apply Fin.ext
        rw [succAbove_val]
        rw [if_pos (by omega)]
      have hR : Work.DSCOH.Norm.readA x a' (Fin.succAbove b q)
          = Tuple.sort x (Fin.succAbove m (⟨(q:ℕ), by have := q.isLt; omega⟩ : Fin (k+1))) := by
        rw [hsv, Work.DSCOH.Norm.readA_head x a'
          (p := (⟨(q:ℕ), by have := q.isLt; omega⟩ : Fin (k+3)))
          (by show (q:ℕ) ≤ (a':ℕ); omega)]
        congr 1
        apply Fin.ext
        simp only [Fin.val_mk]
        rw [succAbove_val]
        rw [if_pos (by show (q:ℕ) < (m:ℕ); omega)]
      rw [hrq, hR, sort_succAbove_apply]
    · -- Case B.b
      have hq_gt : (a:ℕ) < (q:ℕ) := lt_of_not_ge hq_le
      have hrq : Work.DSCOH.Norm.readA (Work.DSCOH.Norm.del x c) a q
          = Work.DSCOH.Norm.tailEmb (Work.DSCOH.Norm.del x c) a
              ⟨(q:ℕ)-1-(a:ℕ), by have := q.isLt; omega⟩ :=
        Work.DSCOH.Norm.readA_tail _ _ hq_le
      have hsv : ((Fin.succAbove b q : Fin (k+3)) : ℕ)
          = if (q:ℕ) < (b:ℕ) then (q:ℕ) else (q:ℕ)+1 := succAbove_val b q
      have hl : (((⟨((Fin.succAbove b q : Fin (k+3)) : ℕ) - 1 - (a':ℕ),
            by have := (Fin.succAbove b q).isLt; have := a'.isLt; omega⟩ : Fin ((k+2)-(a':ℕ))) : ℕ))
          = ((⟨(q:ℕ)-1-(a:ℕ), by have := q.isLt; omega⟩ : Fin ((k+1)-(a:ℕ))) : ℕ)
            + (if ((⟨(q:ℕ)-1-(a:ℕ), by have := q.isLt; omega⟩ : Fin ((k+1)-(a:ℕ))) : ℕ)
                < (j:ℕ) then 0 else 1) := by
        show ((Fin.succAbove b q : Fin (k+3)) : ℕ) - 1 - (a':ℕ)
            = ((q:ℕ)-1-(a:ℕ))
              + (if ((q:ℕ)-1-(a:ℕ)) < ((b:ℕ)-1-(a':ℕ)) then 0 else 1)
        rw [hsv]
        by_cases hqb : (q:ℕ) < (b:ℕ)
        · rw [if_pos hqb]
          rw [if_pos (by omega)]
          omega
        · rw [if_neg hqb]
          rw [if_neg (by omega)]
          omega
      rw [hrq]
      rw [Work.DSCOH.Norm.readA_tail x a' (p := Fin.succAbove b q)
        (by rw [hsv]; by_cases hqb : (q:ℕ) < (b:ℕ)
            · rw [if_pos hqb]; omega
            · rw [if_neg hqb]; omega)]
      rw [← tailEmb_compl_of_gt x c a hca_gt hva j hju
        ⟨(q:ℕ)-1-(a:ℕ), by have := q.isLt; omega⟩
        ⟨((Fin.succAbove b q : Fin (k+3)) : ℕ) - 1 - (a':ℕ),
          by show ((Fin.succAbove b q : Fin (k+3)) : ℕ) - 1 - (a':ℕ) < (k+2) - (a':ℕ)
             rw [hsv]; by_cases hqb : (q:ℕ) < (b:ℕ)
             · rw [if_pos hqb]
               exact Nat.sub_lt_sub_right (by omega) (by have := q.isLt; omega)
             · rw [if_neg hqb]
               rw [show (q:ℕ) + 1 - 1 - (a':ℕ) = (q:ℕ) - (a':ℕ) from by omega]
               exact Nat.sub_lt_sub_right (by omega) (by have := q.isLt; omega)⟩ hl]

end Work.DSCOH.PairingIndex
