import Mathlib
import Submission.Work.Pi6.MSSK.CapThetaBasic
import Submission.Work.SSSR.pieceIso_peel
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSSK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-!
# The coboundary of the top cochain of the last face

`cochainDiff_lastFaceTop`: for a simplex `σ : Δ[t+1] ⟶ Sing B` and `T_σ = Δ[t+1] ×_{Sing B} Sing E`,
the coboundary of the indicator cochain `lastFaceTop` (the simplices over the top simplex of the
LAST face of `Δ[t+1]`) is `(-1)^(t+1)` times the indicator cochain `thetaTop` of the simplices over
the top simplex of `Δ[t+1]`.

The proof splits into

* a purely combinatorial identity about an endomorphism `f` of `⦋t+1⦌` (`delta_sum_lastFace_aux`,
  proved from `LastFaceTop.Cd_sum` below), and
* the translation of the values `lastFaceVal`/`thetaVal` into that combinatorics through
  `SSet.stdSimplex.objEquiv`.

The combinatorics: for `i : Fin (t+2)` let `Cd g i` say that the monotone map `g` is the identity
below `i` and is `·-1` above `i` (i.e. the `i`-th face of `g` is the last face).  The set of such
`i` is either empty, a pair `{i, i+1}` (whose alternating contributions cancel), or the single
top index `t+1` (which happens exactly for `g = id`).
-/

namespace LastFaceTop

/-- `Pd g i`: the monotone map `g` fixes every vertex below `i`. -/
abbrev Pd {t : ℕ} (g : Fin (t+2) → Fin (t+2)) (i : Fin (t+2)) : Prop :=
  ∀ k : Fin (t+2), k.val < i.val → g k = k

/-- `Qd g i`: the monotone map `g` maps every vertex above `i` to its predecessor. -/
abbrev Qd {t : ℕ} (g : Fin (t+2) → Fin (t+2)) (i : Fin (t+2)) : Prop :=
  ∀ k : Fin (t+2), i.val < k.val → (g k).val = k.val - 1

/-- `Cd g i`: the `i`-th face of `g` is the last face, in value form. -/
abbrev Cd {t : ℕ} (g : Fin (t+2) → Fin (t+2)) (i : Fin (t+2)) : Prop := Pd g i ∧ Qd g i

/-- The value form of "the `i`-th face of `f` is the last face". -/
lemma D_iff {t : ℕ} (g : Fin (t+2) → Fin (t+2)) (i : Fin (t+2)) :
    (∀ j : Fin (t+1), g (i.succAbove j) = j.castSucc) ↔ Cd g i := by
  constructor
  · intro h
    constructor
    · intro k hk
      have hki : k < i := Fin.lt_def.mpr hk
      have hstep : i.succAbove (k.castPred (Fin.ne_last_of_lt hki)) = k :=
        Fin.succAbove_castPred_of_lt i k hki
      have hh := congrArg Fin.val (h (k.castPred (Fin.ne_last_of_lt hki)))
      rw [hstep, Fin.castSucc_castPred] at hh
      exact Fin.ext hh
    · intro k hk
      have hk0 : k ≠ 0 := by
        intro h0; rw [h0] at hk; simp only [Fin.val_zero] at hk; omega
      have hle : i ≤ (k.pred hk0).castSucc := by
        rw [Fin.le_def]; simp only [Fin.val_castSucc, Fin.val_pred k hk0]; omega
      have hsucc : i.succAbove (k.pred hk0) = k := by
        rw [Fin.succAbove_of_le_castSucc i (k.pred hk0) hle, Fin.succ_pred k hk0]
      have hh := congrArg Fin.val (h (k.pred hk0))
      rw [hsucc, Fin.val_castSucc, Fin.val_pred k hk0] at hh
      exact hh
  · rintro ⟨hP, hQ⟩ j
    by_cases hj : j.castSucc < i
    · rw [Fin.succAbove_of_castSucc_lt i j hj]
      exact hP j.castSucc hj
    · have hle : i ≤ j.castSucc := le_of_not_gt hj
      rw [Fin.succAbove_of_le_castSucc i j hle]
      apply Fin.ext
      have hle' : i.val < (j.succ).val := by
        rw [Fin.le_def, Fin.val_castSucc] at hle
        rw [Fin.val_succ]; omega
      have hh := hQ j.succ hle'
      rw [hh, Fin.val_succ, Fin.val_castSucc]
      omega

/-- `Cd g i` propagates upwards when `g` fixes `i`. -/
lemma Pd_up {t : ℕ} {g : Fin (t+2) → Fin (t+2)} {i : Fin (t+2)} (h : Pd g i) (hi : g i = i)
    (hne : i ≠ Fin.last (t+1)) : Pd g ((i.castPred hne).succ) := by
  intro k hk
  rw [Fin.val_succ, Fin.coe_castPred] at hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h' | h'
  · exact h k h'
  · rw [Fin.ext h', hi]

lemma Qd_up {t : ℕ} {g : Fin (t+2) → Fin (t+2)} {i : Fin (t+2)} (h : Qd g i)
    (hne : i ≠ Fin.last (t+1)) : Qd g ((i.castPred hne).succ) := by
  intro k hk
  rw [Fin.val_succ, Fin.coe_castPred] at hk
  exact h k (by omega)

lemma Pd_dn {t : ℕ} {g : Fin (t+2) → Fin (t+2)} {i : Fin (t+2)} (h : Pd g i) (h0 : i ≠ 0) :
    Pd g ((i.pred h0).castSucc) := by
  intro k hk
  rw [Fin.val_castSucc, Fin.val_pred i h0] at hk
  exact h k (by omega)

lemma Qd_dn {t : ℕ} {g : Fin (t+2) → Fin (t+2)} {i : Fin (t+2)} (h : Qd g i)
    (hi : (g i).val = i.val - 1) (h0 : i ≠ 0) : Qd g ((i.pred h0).castSucc) := by
  intro k hk
  rw [Fin.val_castSucc, Fin.val_pred i h0] at hk
  have hiv : i.val ≠ 0 := fun hc => h0 (by apply Fin.ext; simpa using hc)
  rcases lt_or_eq_of_le (by omega : i.val ≤ k.val) with h' | h'
  · exact h k h'
  · rw [← Fin.ext h', hi]

lemma Cd_up {t : ℕ} {g : Fin (t+2) → Fin (t+2)} {i : Fin (t+2)} (h : Cd g i) (hi : g i = i)
    (hne : i ≠ Fin.last (t+1)) : Cd g ((i.castPred hne).succ) :=
  ⟨Pd_up h.1 hi hne, Qd_up h.2 hne⟩

lemma Cd_dn {t : ℕ} {g : Fin (t+2) → Fin (t+2)} {i : Fin (t+2)} (h : Cd g i)
    (hi : (g i).val = i.val - 1) (h0 : i ≠ 0) : Cd g ((i.pred h0).castSucc) :=
  ⟨Pd_dn h.1 h0, Qd_dn h.2 hi h0⟩

/-- A monotone `g` with `Cd g i` and `i` below the top sends `i` to `i` or to `i - 1`. -/
lemma Cd_val_bound {t : ℕ} {g : Fin (t+2) → Fin (t+2)} (hg : Monotone g) {i : Fin (t+2)}
    (h : Cd g i) (hlt : i.val < t+1) : g i = i ∨ (g i).val = i.val - 1 := by
  have hne : i ≠ Fin.last (t+1) := by
    intro hc; rw [hc] at hlt; simp only [Fin.val_last] at hlt; omega
  have hup : (g ((i.castPred hne).succ)).val = i.val := by
    have := h.2 ((i.castPred hne).succ) (by rw [Fin.val_succ, Fin.coe_castPred]; omega)
    rw [Fin.val_succ, Fin.coe_castPred] at this
    omega
  have hupper : (g i).val ≤ i.val := by
    have hmono : g i ≤ g ((i.castPred hne).succ) :=
      hg (by rw [Fin.le_def, Fin.val_succ, Fin.coe_castPred]; omega)
    rw [Fin.le_def, hup] at hmono
    exact hmono
  have hlower : i.val - 1 ≤ (g i).val := by
    rcases Nat.eq_zero_or_pos i.val with h0 | h0
    · omega
    · have h0' : i ≠ 0 := fun hc => by rw [hc] at h0; simp at h0
      have hk : ((i.pred h0').castSucc).val = i.val - 1 := by
        rw [Fin.val_castSucc, Fin.val_pred i h0']
      have hP := h.1 ((i.pred h0').castSucc) (by rw [hk]; omega)
      have hmono : g ((i.pred h0').castSucc) ≤ g i :=
        hg (by rw [Fin.le_def, hk]; omega)
      rw [hP, Fin.le_def, hk] at hmono
      exact hmono
  rcases eq_or_ne (g i).val i.val with he | hne2
  · exact Or.inl (Fin.ext he)
  · exact Or.inr (by omega)

/-- Two distinct indices in the support differ by exactly one. -/
lemma Cd_adjacent {t : ℕ} {g : Fin (t+2) → Fin (t+2)} {i j : Fin (t+2)} (hi : Cd g i)
    (hj : Cd g j) (hne : i ≠ j) : i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · left
    by_contra hcon
    have hk : i.val + 1 < j.val := by omega
    let k : Fin (t+2) := ⟨i.val + 1, by have := j.isLt; omega⟩
    have hkval : k.val = i.val + 1 := rfl
    have h1 : g k = k := hj.1 k (by rw [hkval]; exact hk)
    have h2 : (g k).val = k.val - 1 := hi.2 k (by rw [hkval]; omega)
    rw [h1, hkval] at h2
    omega
  · exact absurd (Fin.ext h) hne
  · right
    by_contra hcon
    have hk : j.val + 1 < i.val := by omega
    let k : Fin (t+2) := ⟨j.val + 1, by have := i.isLt; omega⟩
    have hkval : k.val = j.val + 1 := rfl
    have h1 : g k = k := hi.1 k (by rw [hkval]; exact hk)
    have h2 : (g k).val = k.val - 1 := hj.2 k (by rw [hkval]; omega)
    rw [h1, hkval] at h2
    omega

/-- If the top index is in the support and `g ≠ id`, then so is the index just below it. -/
lemma Cd_last_pred {t : ℕ} {g : Fin (t+2) → Fin (t+2)} (hg : Monotone g)
    (h : Cd g (Fin.last (t+1))) (hne : g ≠ id) : Cd g (⟨t, by omega⟩ : Fin (t+2)) := by
  show Cd g (Fin.castSucc (Fin.last t))
  have h0 : (Fin.last (t+1) : Fin (t+2)) ≠ 0 := by
    intro hc; have := congrArg Fin.val hc; simp only [Fin.val_last, Fin.val_zero] at this; omega
  have hgl : g (Fin.last (t+1)) ≠ Fin.last (t+1) := by
    intro hc
    refine hne (funext fun x => ?_)
    rcases eq_or_ne x (Fin.last (t+1)) with hx | hx
    · subst hx; simpa using hc
    · show g x = x
      refine h.1 x ?_
      simp only [Fin.val_last]
      have hx' : x.val ≠ t + 1 := fun hc2 => hx (Fin.ext (by rw [hc2, Fin.val_last]))
      have := x.isLt
      omega
  have hm : (Fin.castSucc (Fin.last t) : Fin (t+2)).val = t := by
    rw [Fin.val_castSucc, Fin.val_last]
  have hP : g (Fin.castSucc (Fin.last t)) = (Fin.castSucc (Fin.last t) : Fin (t+2)) :=
    h.1 _ (by rw [hm, Fin.val_last]; omega)
  have hmono : g (Fin.castSucc (Fin.last t)) ≤ g (Fin.last (t+1)) := by
    apply hg
    rw [Fin.le_def]
    simp only [Fin.val_castSucc, Fin.val_last]
    exact Nat.le_succ t
  rw [hP, Fin.le_def, hm] at hmono
  have hval : (g (Fin.last (t+1))).val = t := by
    have hle : (g (Fin.last (t+1))).val ≤ t := by
      rcases Nat.lt_or_ge (g (Fin.last (t+1))).val (t + 1) with hlt | hge
      · omega
      · have hvv : (g (Fin.last (t+1))).val = t + 1 := by
          have h3 := (g (Fin.last (t+1))).isLt
          omega
        exact absurd (Fin.ext (by rw [hvv, Fin.val_last])) hgl
    exact le_antisymm hle hmono
  have heq : (((Fin.last (t+1)) : Fin (t+2)).pred h0).castSucc = Fin.castSucc (Fin.last t) := by
    apply Fin.ext
    rw [Fin.val_castSucc, Fin.val_pred, Fin.val_last, Fin.val_castSucc, Fin.val_last]
    simp only [Nat.add_sub_cancel]
  have hmain : (g (Fin.last (t+1))).val = ((Fin.last (t+1)) : Fin (t+2)).val - 1 := by
    rw [hval, Fin.val_last]
    simp only [Nat.add_sub_cancel]
  rw [← heq]
  exact Cd_dn h hmain h0

/-- **The combinatorial core**: the alternating sum over the faces of the indicator of
"the `i`-th face of `g` is the last face". -/
lemma Cd_sum (R : Type) [CommRing R] {t : ℕ} (g : Fin (t+2) → Fin (t+2)) (hg : Monotone g) :
    (∑ i : Fin (t+2), (-1:R)^(i:ℕ) * (if Cd g i then (1:R) else 0))
      = (-1:R)^(t+1) * (if g = id then (1:R) else 0) := by
  by_cases hid : g = id
  · have hkey : ∀ i : Fin (t+2), Cd (id : Fin (t+2) → Fin (t+2)) i ↔ i = Fin.last (t+1) := by
      intro i
      constructor
      · intro h
        by_contra hne'
        have hne2 : ((i.castPred hne').succ).val ≠ ((i.castPred hne').succ).val - 1 := by
          rw [Fin.val_succ, Fin.coe_castPred, Nat.add_sub_cancel]
          exact Nat.succ_ne_self i.val
        have hk : i.val < ((i.castPred hne').succ).val := by
          rw [Fin.val_succ, Fin.coe_castPred]; omega
        refine hne2 ?_
        simpa only [id_eq] using h.2 ((i.castPred hne').succ) hk
      · intro h
        subst h
        exact ⟨fun k _ => rfl, fun k hk => by
          simp only [Fin.val_last] at hk
          omega⟩
    have hsum : (∑ i : Fin (t+2),
        (-1:R)^(i:ℕ) * (if Cd (id : Fin (t+2) → Fin (t+2)) i then (1:R) else 0))
        = (-1:R)^(t+1) := by
      have h1 : (∑ i : Fin (t+2),
          (-1:R)^(i:ℕ) * (if Cd (id : Fin (t+2) → Fin (t+2)) i then (1:R) else 0))
          = (∑ i : Fin (t+2), (-1:R)^(i:ℕ) * (if i = Fin.last (t+1) then (1:R) else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hc : Cd (id : Fin (t+2) → Fin (t+2)) i
        · rw [ite_eq_left hc, ite_eq_left ((hkey i).mp hc)]
        · rw [ite_eq_right hc, ite_eq_right (fun hh => hc ((hkey i).mpr hh))]
      rw [h1]
      rw [Finset.sum_eq_single (Fin.last (t+1))]
      · simp
      · intro b _ hb
        rw [ite_eq_right hb, mul_zero]
      · intro hb
        exact absurd (Finset.mem_univ (Fin.last (t+1))) hb
    rw [hid]
    simpa using hsum
  · have hsum : (∑ i : Fin (t+2), (-1:R)^(i:ℕ) * (if Cd g i then (1:R) else 0)) = 0 := by
      by_cases hI : ∃ i : Fin (t+2), Cd g i
      · obtain ⟨i0, hi0⟩ := hI
        have hex : ∃ i1 : Fin (t+2), Cd g i1 ∧ i1 ≠ i0 := by
          rcases eq_or_ne i0 (Fin.last (t+1)) with hlast | hlast
          · subst hlast
            have h0' : (Fin.last (t+1) : Fin (t+2)) ≠ 0 := by
              intro hc; have := congrArg Fin.val hc
              simp only [Fin.val_last, Fin.val_zero] at this; omega
            refine ⟨(((Fin.last (t+1)) : Fin (t+2)).pred h0').castSucc,
              Cd_last_pred hg hi0 hid, ?_⟩
            intro hc'
            have hv := congrArg Fin.val hc'
            simp only [Fin.val_castSucc, Fin.val_pred, Fin.val_last] at hv
            omega
          · rcases eq_or_ne (g i0) i0 with hfix | hfix
            · refine ⟨(i0.castPred hlast).succ, Cd_up hi0 hfix hlast, ?_⟩
              intro hc'
              have hv := congrArg Fin.val hc'
              rw [Fin.val_succ, Fin.coe_castPred] at hv
              omega
            · have hlt : i0.val < t+1 := by
                have h2 : i0.val ≠ t + 1 := fun hc => hlast (Fin.ext (by rw [hc, Fin.val_last]))
                have h3 := i0.isLt
                omega
              have hval := (Cd_val_bound hg hi0 hlt).resolve_left hfix
              have h0' : i0 ≠ 0 := by
                intro hc
                subst hc
                simp only [Fin.val_zero] at hval
                exact hfix (Fin.ext (by rw [hval]; rfl))
              refine ⟨(i0.pred h0').castSucc, Cd_dn hi0 hval h0', ?_⟩
              intro hc'
              have hv := congrArg Fin.val hc'
              simp only [Fin.val_castSucc, Fin.val_pred i0 h0'] at hv
              have hge : 1 ≤ i0.val := by
                have h2 : i0.val ≠ 0 := fun hc => h0' (Fin.ext (by simpa using hc))
                omega
              omega
        obtain ⟨i1, hi1, hne10⟩ := hex
        have hsub : ∀ j : Fin (t+2), Cd g j → j = i0 ∨ j = i1 := by
          intro j hj
          by_cases hj0 : j = i0
          · exact Or.inl hj0
          by_cases hj1 : j = i1
          · exact Or.inr hj1
          exfalso
          have ha := Cd_adjacent hi0 hj (fun hc => hj0 hc.symm)
          have hb := Cd_adjacent hi1 hj (fun hc => hj1 hc.symm)
          have hab := Cd_adjacent hi1 hi0 hne10
          clear hne10 hj0 hj1
          omega
        have hs : (∑ j : Fin (t+2), (-1:R)^(j:ℕ) * (if Cd g j then (1:R) else 0))
            = ∑ j ∈ ({i0, i1} : Finset (Fin (t+2))),
                (-1:R)^(j:ℕ) * (if Cd g j then (1:R) else 0) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro x _ hx
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [ite_eq_right (fun hc => hx (hsub x hc)), mul_zero]
        rw [hs, Finset.sum_insert (by rw [Finset.mem_singleton]; exact fun hc => hne10 hc.symm),
          Finset.sum_singleton]
        rw [ite_eq_left hi0, ite_eq_left hi1, mul_one, mul_one]
        rcases Cd_adjacent hi0 hi1 (fun hc => hne10 hc.symm) with hab | hab
        · rw [← hab, pow_succ]; ring
        · rw [← hab, pow_succ]; ring
      · push Not at hI
        rw [Finset.sum_eq_zero]
        intro j _
        rw [ite_eq_right (hI j), mul_zero]
    rw [ite_eq_right hid, mul_zero]
    exact hsum

/-! ### Passing from an endomorphism of `⦋t+1⦌` to a monotone map of `Fin (t+2)` -/

lemma delta_toOrderHom_succAbove {t : ℕ} (i : Fin (t+2)) (j : Fin (t+1)) :
    (SimplexCategory.δ (n := t) i).toOrderHom j = i.succAbove j := by
  rw [show (SimplexCategory.δ (n := t) i).toOrderHom
      = ⇑(ConcreteCategory.hom (SimplexCategory.δ (n := t) i)) from rfl]
  rw [SimplexCategory.coe_δ]

lemma delta_last_toOrderHom {t : ℕ} (j : Fin (t+1)) :
    (SimplexCategory.δ (n := t) (Fin.last (t+1))).toOrderHom j = j.castSucc := by
  rw [show (SimplexCategory.δ (n := t) (Fin.last (t+1))).toOrderHom
      = ⇑(ConcreteCategory.hom (SimplexCategory.δ (n := t) (Fin.last (t+1)))) from rfl]
  rw [SimplexCategory.coe_δ]
  exact Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last j)

/-- The condition "the `i`-th face of `f` is the last face", in value form. -/
lemma delta_comp_eq_last_iff {t : ℕ} (f : (⦋t+1⦌ : SimplexCategory) ⟶ ⦋t+1⦌) (i : Fin (t+2)) :
    (SimplexCategory.δ (n := t) i ≫ f = SimplexCategory.δ (n := t) (Fin.last (t+1)))
      ↔ (∀ j : Fin (t+1), f.toOrderHom (i.succAbove j) = j.castSucc) := by
  constructor
  · intro h j
    have h2 := congrArg (fun (φ : (⦋t⦌ : SimplexCategory) ⟶ ⦋t+1⦌) => φ.toOrderHom j) h
    rw [SimplexCategory.comp_toOrderHom] at h2
    simp only [OrderHom.comp_coe, Function.comp_apply] at h2
    rw [delta_toOrderHom_succAbove i j, delta_last_toOrderHom j] at h2
    exact h2
  · intro h
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    rw [SimplexCategory.comp_toOrderHom]
    simp only [OrderHom.comp_coe, Function.comp_apply]
    rw [delta_toOrderHom_succAbove i j, delta_last_toOrderHom j]
    exact h j

/-- The identity of `⦋t+1⦌` is the identity monotone map. -/
lemma hom_eq_id_iff {t : ℕ} (f : (⦋t+1⦌ : SimplexCategory) ⟶ ⦋t+1⦌) :
    (⇑(f.toOrderHom) = id) ↔ f = 𝟙 ⦋t+1⦌ := by
  constructor
  · intro h
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    simpa using h
  · intro h
    subst h
    rfl

/-- **The combinatorial identity in the form used below.** -/
lemma delta_sum_lastFace_aux (R : Type) [CommRing R] (t : ℕ)
    (f : (⦋t+1⦌ : SimplexCategory) ⟶ ⦋t+1⦌) :
    (∑ i : Fin (t+2),
        (-1:R)^(i:ℕ) * (if SimplexCategory.δ (n := t) i ≫ f
            = SimplexCategory.δ (n := t) (Fin.last (t+1)) then (1:R) else 0))
      = (-1:R)^(t+1) * (if f = 𝟙 ⦋t+1⦌ then (1:R) else 0) := by
  have hmono : Monotone (⇑(f.toOrderHom) : Fin (t+2) → Fin (t+2)) := f.toOrderHom.monotone
  have hkey : ∀ i : Fin (t+2), Cd (⇑(f.toOrderHom)) i ↔
      (SimplexCategory.δ (n := t) i ≫ f = SimplexCategory.δ (n := t) (Fin.last (t+1))) := by
    intro i
    rw [delta_comp_eq_last_iff f i]
    exact (D_iff (⇑(f.toOrderHom)) i).symm
  have h1 : (∑ i : Fin (t+2),
        (-1:R)^(i:ℕ) * (if Cd (⇑(f.toOrderHom)) i then (1:R) else 0))
      = (∑ i : Fin (t+2),
          (-1:R)^(i:ℕ) * (if SimplexCategory.δ (n := t) i ≫ f
              = SimplexCategory.δ (n := t) (Fin.last (t+1)) then (1:R) else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hc : Cd (⇑(f.toOrderHom)) i
    · rw [ite_eq_left hc, ite_eq_left ((hkey i).mp hc)]
    · rw [ite_eq_right hc, ite_eq_right (fun hh => hc ((hkey i).mpr hh))]
  rw [← h1, Cd_sum R (⇑(f.toOrderHom)) hmono]
  congr 1
  by_cases hf : f = 𝟙 ⦋t+1⦌
  · rw [ite_eq_left hf, ite_eq_left ((hom_eq_id_iff f).mpr hf)]
  · rw [ite_eq_right hf, ite_eq_right (fun hh => hf ((hom_eq_id_iff f).mp hh))]

/-! ### The simplification of `lastFaceVal` and `thetaVal` -/

/-- Under `objEquiv`, the `i`-th face of a top simplex of `Δ[n+1]` corresponds to the composite
of the underlying monotone map with `δ i`. -/
lemma objEquiv_deltaTop (n : ℕ) (i : Fin (n+2))
    (a : (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) _⦋n+1⦌) :
    SSet.stdSimplex.objEquiv (((SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})).δ i a)
      = SimplexCategory.δ i ≫ SSet.stdSimplex.objEquiv a := by
  conv_lhs => rw [← Equiv.symm_apply_apply SSet.stdSimplex.objEquiv a]
  rw [SSet.stdSimplex.δ_objEquiv_symm_apply]
  rw [Equiv.apply_symm_apply]

/-- `lastFaceVal` is the indicator of the simplices of `T_σ` whose projection is the top simplex of
the last face of `Δ[t+1]`, read through `objEquiv`. -/
lemma lastFaceVal_eq_ite (R : Type) [CommRing R] {t : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (x : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t⦌) :
    lastFaceVal R p σ x
      = (if SSet.stdSimplex.objEquiv (proj p σ x)
            = SimplexCategory.δ (Fin.last (t+1)) then (1:R) else 0) := by
  rw [show lastFaceVal R p σ x
      = (if proj p σ x
            = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (Fin.last (t+1)))
          then (1:R) else 0) from rfl]
  by_cases h : SSet.stdSimplex.objEquiv (proj p σ x) = SimplexCategory.δ (Fin.last (t+1))
  · have h' : proj p σ x
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (Fin.last (t+1))) := by
      rw [← h, Equiv.symm_apply_apply]
    rw [ite_eq_left h', ite_eq_left h]
  · have h' : ¬ (proj p σ x
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (Fin.last (t+1)))) := by
      intro hc; exact h (by rw [hc, Equiv.apply_symm_apply])
    rw [ite_eq_right h', ite_eq_right h]

/-- `thetaVal` is the indicator of the simplices of `T_σ` whose projection is the top simplex of
`Δ[s]`, read through `objEquiv`. -/
lemma thetaVal_eq_ite (R : Type) [CommRing R] {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (x : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s⦌) :
    thetaVal R p σ x
      = (if SSet.stdSimplex.objEquiv (proj p σ x)
            = 𝟙 (SimplexCategory.mk s) then (1:R) else 0) := by
  rw [show thetaVal R p σ x
      = (if proj p σ x = topS s then (1:R) else 0) from rfl]
  by_cases h : SSet.stdSimplex.objEquiv (proj p σ x) = 𝟙 (SimplexCategory.mk s)
  · have h' : proj p σ x = topS s := by
      rw [topS, ← h, Equiv.symm_apply_apply]
    rw [ite_eq_left h', ite_eq_left h]
  · have h' : ¬ (proj p σ x = topS s) := by
      intro hc; exact h (by rw [hc, topS, Equiv.apply_symm_apply])
    rw [ite_eq_right h', ite_eq_right h]

/-- **The value of the coboundary of `lastFaceTop` on a top simplex**: the alternating sum of the
values of `lastFaceVal` on the faces. -/
lemma altSum_lastFaceVal (R : Type) [CommRing R] [Nontrivial R] {t : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t+1⦌) :
    (∑ i : Fin (t+2),
        (-1:R)^(i:ℕ) * lastFaceVal R p σ ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).δ i w))
      = (-1:R)^(t+1) * thetaVal R p σ w := by
  set f : ⦋t+1⦌ ⟶ ⦋t+1⦌ := SSet.stdSimplex.objEquiv (proj p σ w) with hf
  have hlast : ∀ i : Fin (t+2),
      lastFaceVal R p σ ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).δ i w)
        = (if SimplexCategory.δ i ≫ f = SimplexCategory.δ (Fin.last (t+1))
            then (1:R) else 0) := by
    intro i
    have hproj : SSet.stdSimplex.objEquiv
          (proj p σ ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).δ i w))
        = SimplexCategory.δ i ≫ f := by
      rw [show proj p σ ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).δ i w)
          = (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}).δ i (proj p σ w)
          from proj_δ p σ w i]
      rw [objEquiv_deltaTop, hf]
    rw [lastFaceVal_eq_ite, hproj]
  have htheta : thetaVal R p σ w = (if f = 𝟙 ⦋t+1⦌ then (1:R) else 0) := by
    rw [thetaVal_eq_ite, hf]
  calc (∑ i : Fin (t+2),
        (-1:R)^(i:ℕ) * lastFaceVal R p σ ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).δ i w))
      = (∑ i : Fin (t+2),
          (-1:R)^(i:ℕ) * (if SimplexCategory.δ i ≫ f = SimplexCategory.δ (Fin.last (t+1))
              then (1:R) else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hlast i]
    _ = (-1:R)^(t+1) * (if f = 𝟙 ⦋t+1⦌ then (1:R) else 0) :=
        delta_sum_lastFace_aux R t f
    _ = (-1:R)^(t+1) * thetaVal R p σ w := by rw [htheta]

end LastFaceTop

open LastFaceTop

/-- **The coboundary of the top cochain of the last face.** -/
theorem cochainDiff_lastFaceTop (R : Type) [CommRing R] [Nontrivial R] {E B : Type}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Cohomology.cochainDiff R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.lastFaceTop R p σ)
      = (-1 : R) ^ (t+1) • Work.Pi6.MSSK.thetaTop R p σ := by
  apply Work.Cohomology.genEval_ext
  intro w
  rw [Work.Cohomology.genEval_cochainDiff, Work.Cohomology.genEval_smul]
  simp only [genEval_lastFaceTop, genEval_thetaTop, smul_eq_mul]
  exact altSum_lastFaceVal R p σ w

end

end Work.Pi6.MSSK
