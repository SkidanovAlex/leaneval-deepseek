import Mathlib
import Submission.Work.Pi6.MSS.AssembleDefs
import Submission.Work.Pi6.MSS.PagesComp
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.MSS.Pages
import Submission.Work.Pi6.MSS.convPage
import Submission.Work.Pi6.MSS.mulEq
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The concrete multiplicative cohomological Serre spectral sequence of a filtered complex

This file assembles the page data `Work.Pi6.MSS.PagesData` of a filtered cochain complex with a
product `W : CohFilt 𝕜` into the bidegree indexing `(s, q)` with total degree `n = s + q` used by
the interface `Work.Pi6.CohSS` (a first-quadrant cohomological spectral sequence with a product).

The bidegree `a : ℤ × ℤ` is translated into the `ℕ`-indices of the concrete pages by
* `EI a = a.1.toNat` (the filtration index, shifted by one off the first quadrant so that the
  corresponding page is a subsingleton — this realises `quad`),
* `EN a = (a.1 + a.2).toNat` (the total degree).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits
open Classical
attribute [local instance] Classical.propDecidable

noncomputable section

variable (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜)

/-! ## 1. Bidegree bookkeeping -/

/-- Bidegrees in the first quadrant. -/
abbrev Enn (a : ℤ × ℤ) : Prop := 0 ≤ a.1 ∧ 0 ≤ a.2

/-- The filtration index of a bidegree; off the first quadrant it is shifted by one so that the
corresponding page is a subsingleton. -/
abbrev EI (a : ℤ × ℤ) : ℕ := a.1.toNat + (if 0 ≤ a.1 ∧ 0 ≤ a.2 then 0 else 1)

/-- The total degree of a bidegree. -/
abbrev EN (a : ℤ × ℤ) : ℕ := if 0 ≤ a.1 then (a.1 + a.2).toNat else 0

/-- The page `E_r^{a}` of the spectral sequence: the concrete subquotient `pEraw`. -/
abbrev mssE (r : ℕ) (a : ℤ × ℤ) : ModuleCat 𝕜 := pEraw 𝕜 W r (EI a) (EN a)

lemma Enn_pair (s q : ℕ) : Enn ((s : ℤ), (q : ℤ)) :=
  ⟨Int.natCast_nonneg s, Int.natCast_nonneg q⟩

lemma Enn_add {a b : ℤ × ℤ} (ha : Enn a) (hb : Enn b) : Enn (a + b) :=
  ⟨add_nonneg ha.1 hb.1, add_nonneg ha.2 hb.2⟩

lemma Enn_of_nonneg {a : ℤ × ℤ} (h : Enn a) : EI a = a.1.toNat := by
  simp only [EI, if_pos h, Nat.add_zero]

lemma EN_of_nonneg {a : ℤ × ℤ} (h : Enn a) : EN a = (a.1 + a.2).toNat := by
  simp only [EN, if_pos h.1]

lemma EI_pair (s q : ℕ) : EI ((s : ℤ), (q : ℤ)) = s := by
  rw [Enn_of_nonneg (Enn_pair s q), Int.toNat_natCast]

lemma EN_pair (s q : ℕ) : EN ((s : ℤ), (q : ℤ)) = s + q := by
  rw [EN_of_nonneg (Enn_pair s q),
    show ((s : ℤ) + (q : ℤ)) = ((s + q : ℕ) : ℤ) from by push_cast; ring, Int.toNat_natCast]

lemma fst_add_vr (a : ℤ × ℤ) (r : ℕ) : (a + vr r).1 = a.1 + (r : ℤ) := rfl
lemma snd_add_vr (a : ℤ × ℤ) (r : ℕ) : (a + vr r).2 = a.2 + (1 - (r : ℤ)) := rfl
lemma fst_sub_vr (a : ℤ × ℤ) (r : ℕ) : (a - vr r).1 = a.1 - (r : ℤ) := rfl
lemma snd_sub_vr (a : ℤ × ℤ) (r : ℕ) : (a - vr r).2 = a.2 - (1 - (r : ℤ)) := rfl

lemma add_vr_sum (a : ℤ × ℤ) (r : ℕ) : (a + vr r).1 + (a + vr r).2 = a.1 + a.2 + 1 := by
  simp only [fst_add_vr, snd_add_vr]; ring

lemma sub_vr_sum (a : ℤ × ℤ) (r : ℕ) : (a - vr r).1 + (a - vr r).2 = a.1 + a.2 - 1 := by
  simp only [fst_sub_vr, snd_sub_vr]; ring

lemma EN_add_vr (r : ℕ) {a : ℤ × ℤ} (ha : Enn a) : EN a + 1 = EN (a + vr r) := by
  rw [EN_of_nonneg ha]
  show (a.1 + a.2).toNat + 1
    = (if 0 ≤ (a + vr r).1 then ((a + vr r).1 + (a + vr r).2).toNat else 0)
  rw [if_pos (by rw [fst_add_vr]; linarith [ha.1, Int.natCast_nonneg r]), add_vr_sum,
    show a.1 + a.2 + 1 = (a.1 + a.2) + 1 from rfl,
    Int.toNat_add (add_nonneg ha.1 ha.2) (by norm_num : (0 : ℤ) ≤ 1), Int.toNat_one]

lemma EI_add_vr (r : ℕ) {a : ℤ × ℤ} (ha : Enn a) (hb : Enn (a + vr r)) :
    EI a + r = EI (a + vr r) := by
  rw [Enn_of_nonneg hb, Enn_of_nonneg ha]
  show a.1.toNat + r = (a + vr r).1.toNat
  rw [fst_add_vr, Int.toNat_add ha.1 (Int.natCast_nonneg r), Int.toNat_natCast]

lemma EN_sub_vr (r : ℕ) {a : ℤ × ℤ} (ha : Enn a) (hb : Enn (a - vr r)) :
    EN a - 1 = EN (a - vr r) := by
  have h3 : 1 ≤ a.1 + a.2 := by
    have h1 := hb.1; rw [fst_sub_vr] at h1
    have h2 := hb.2; rw [snd_sub_vr] at h2
    linarith [Int.natCast_nonneg r]
  rw [EN_of_nonneg ha]
  show (a.1 + a.2).toNat - 1
    = (if 0 ≤ (a - vr r).1 then ((a - vr r).1 + (a - vr r).2).toNat else 0)
  rw [if_pos hb.1, sub_vr_sum]
  omega

lemma EI_sub_vr (r : ℕ) {a : ℤ × ℤ} (ha : Enn a) (hb : Enn (a - vr r)) :
    EI a - r = EI (a - vr r) := by
  rw [Enn_of_nonneg hb, Enn_of_nonneg ha]
  show a.1.toNat - r = (a - vr r).1.toNat
  rw [fst_sub_vr,
    show a.1 - (r : ℤ) = ((a.1.toNat : ℤ) - (r : ℤ)) from by rw [Int.toNat_of_nonneg ha.1],
    Int.toNat_sub]

lemma EI_add {a b : ℤ × ℤ} (ha : Enn a) (hb : Enn b) : EI a + EI b = EI (a + b) := by
  rw [Enn_of_nonneg (Enn_add ha hb), Enn_of_nonneg ha, Enn_of_nonneg hb]
  show a.1.toNat + b.1.toNat = (a.1 + b.1).toNat
  exact (Int.toNat_add ha.1 hb.1).symm

lemma EN_add {a b : ℤ × ℤ} (ha : Enn a) (hb : Enn b) : EN a + EN b = EN (a + b) := by
  rw [EN_of_nonneg (Enn_add ha hb), EN_of_nonneg ha, EN_of_nonneg hb]
  show (a.1 + a.2).toNat + (b.1 + b.2).toNat = (a.1 + b.1 + (a.2 + b.2)).toNat
  rw [show a.1 + b.1 + (a.2 + b.2) = (a.1 + a.2) + (b.1 + b.2) from by ring]
  exact (Int.toNat_add (add_nonneg ha.1 ha.2) (add_nonneg hb.1 hb.2)).symm

/-! ## 2. Vanishing off the first quadrant -/

lemma subsingleton_pEraw_of (r s n : ℕ) (h : n + 1 ≤ s) : Subsingleton (pEraw 𝕜 W r s n) := by
  have hF : W.F s n = ⊥ := conv_F_eq_bot W h
  have hZ : pZ 𝕜 W r s n = ⊥ := by
    rw [eq_bot_iff]; intro x hx; rw [← hF]; exact hx.1
  rw [pEraw, hZ]; infer_instance

lemma EN_lt_EI_of_not {a : ℤ × ℤ} (h : ¬ Enn a) : EN a + 1 ≤ EI a := by
  by_cases h1 : 0 ≤ a.1
  · have h2 : ¬ (0 ≤ a.2) := fun h2 => h ⟨h1, h2⟩
    have hEI : EI a = a.1.toNat + 1 := by rw [EI, if_neg h]
    have hEN : EN a = (a.1 + a.2).toNat := by rw [EN, if_pos h1]
    rw [hEI, hEN]
    have h3 : a.1 + a.2 ≤ a.1 := by omega
    have h4 := Int.toNat_le_toNat h3
    omega
  · have hEI : EI a = 1 := by
      simp only [EI, if_neg h, (Int.toNat_eq_zero.mpr (by omega : a.1 ≤ 0) : a.1.toNat = 0),
        Nat.zero_add]
    have hEN : EN a = 0 := by rw [EN, if_neg h1]
    rw [hEI, hEN]

lemma subsingleton_mssE (r : ℕ) {a : ℤ × ℤ} (h : ¬ Enn a) : Subsingleton (mssE 𝕜 W r a) :=
  subsingleton_pEraw_of 𝕜 W r (EI a) (EN a) (EN_lt_EI_of_not h)

lemma isZero_mssE (r : ℕ) {a : ℤ × ℤ} (h : a.1 < 0 ∨ a.2 < 0) : IsZero (mssE 𝕜 W r a) := by
  have h' : ¬ Enn a := by rintro ⟨h1, h2⟩; rcases h with h | h <;> omega
  haveI := subsingleton_mssE 𝕜 W r h'
  exact ModuleCat.isZero_of_subsingleton _

lemma pD_eq_zero_of (r s n : ℕ) (h : n + 1 + 1 ≤ s + r) : pD 𝕜 W r s n = 0 := by
  haveI : Subsingleton (pEraw 𝕜 W r (s + r) (n + 1)) :=
    subsingleton_pEraw_of 𝕜 W r (s + r) (n + 1) h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

lemma ker_pD_eq_top (r s n : ℕ) (h : n + 1 + 1 ≤ s + r) :
    LinearMap.ker (pD 𝕜 W r s n).hom = ⊤ := by
  rw [pD_eq_zero_of 𝕜 W r s n h, ModuleCat.hom_zero, LinearMap.ker_zero]

lemma pEcast_hom_id (r : ℕ) {s n : ℕ} (h : s = s) (h' : n = n) :
    (pEcast 𝕜 W r h h').hom = 𝟙 (pEraw 𝕜 W r s n) := by
  rw [Subsingleton.elim h rfl, Subsingleton.elim h' rfl]
  simp [pEcast, eqToIso_refl]

lemma pD_pEcastNat (r s s' n n' : ℕ) (e1 : s = s') (e2 : n = n')
    (e3 : s + r = s' + r) (e4 : n + 1 = n' + 1) :
    pD 𝕜 W r s n ≫ (pEcast 𝕜 W r e3 e4).hom = (pEcast 𝕜 W r e1 e2).hom ≫ pD 𝕜 W r s' n' := by
  cases e1; cases e2
  rw [pEcast_hom_id, pEcast_hom_id]; simp

lemma pDen_succ_le (r s n : ℕ) (hs : s < r) : pDen 𝕜 W (r + 1) s n ≤ pDen 𝕜 W r s n := by
  refine sup_le ?_ ?_
  · exact le_trans (pd_pZ_anti (𝕜 := 𝕜) (W := W) (r := r - 1) (r' := r) (s := s + 1) (s' := s + 1)
      (by omega) le_rfl) le_sup_left
  · have h : pB 𝕜 W (r + 1) s n = pB 𝕜 W r s n := by
      have h1 : s + 1 - r = 0 := by omega
      have h2 : s + 1 - (r + 1) = 0 := by omega
      rw [pB, pB, h1, h2]
    rw [h]; exact le_sup_right

/-- For `s < r` the incoming differential of the concrete pages vanishes, so the projection
`pd_proj r s n` is injective. -/
lemma pd_proj_injective_low (r s n : ℕ) (hr : 2 ≤ r) (hs : s < r) :
    Function.Injective (pd_proj 𝕜 W r s n) := by
  intro x y hxy
  have h1 : pd_proj 𝕜 W r s n (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h2 : x - y = 0 := by
    set a := Function.surjInv (pd_Phi_surj 𝕜 W r s n) (x - y) with ha
    have hPhi : pd_Phi 𝕜 W r s n a = x - y := Function.surjInv_eq (pd_Phi_surj 𝕜 W r s n) _
    have hpf : pd_pFun 𝕜 W r s n a = 0 := by
      rw [← pd_proj_eq_of 𝕜 W r s n a, hPhi]
      exact h1
    have hmem : a.1 ∈ pDen 𝕜 W r s n ⊔ pDen 𝕜 W (r + 1) s n :=
      (pd_pFun_zero_iff 𝕜 W r s n a).mp hpf
    have hmem' : a.1 ∈ pDen 𝕜 W r s n := by
      rcases Submodule.mem_sup.mp hmem with ⟨u, hu, v, hv, huv⟩
      have h : a.1 ∈ pDen 𝕜 W r s n ⊔ pDen 𝕜 W r s n :=
        Submodule.mem_sup.mpr ⟨u, hu, v, pDen_succ_le 𝕜 W r s n hs hv, huv⟩
      simpa using h
    have hz : pd_Phi 𝕜 W r s n a = 0 := (pd_Phi_ker_iff 𝕜 W r s n a).mpr hmem'
    rw [hPhi] at hz
    exact hz
  exact sub_eq_zero.mp h2

/-! ## 3. The differential -/

/-- The differential `E_r^{a} → E_r^{a + (r, 1-r)}` of the concrete pages, with the index casts. -/
def mssDStep (r : ℕ) {a : ℤ × ℤ} (h1 : EI a + r = EI (a + vr r))
    (h2 : EN a + 1 = EN (a + vr r)) : mssE 𝕜 W r a ⟶ mssE 𝕜 W r (a + vr r) :=
  pD 𝕜 W r (EI a) (EN a) ≫ (pEcast 𝕜 W r h1 h2).hom

def mssDMain (r : ℕ) (a : ℤ × ℤ) : mssE 𝕜 W r a ⟶ mssE 𝕜 W r (a + vr r) :=
  if ha : 0 ≤ a.1 ∧ 0 ≤ a.2 then
    (if hb : 0 ≤ (a + vr r).1 ∧ 0 ≤ (a + vr r).2 then
      mssDStep 𝕜 W r (EI_add_vr r ha hb) (EN_add_vr r ha)
    else 0)
  else 0

lemma mssDMain_pos (r : ℕ) {a : ℤ × ℤ} (ha : Enn a) (hb : Enn (a + vr r)) :
    mssDMain 𝕜 W r a = mssDStep 𝕜 W r (EI_add_vr r ha hb) (EN_add_vr r ha) := by
  rw [mssDMain, dif_pos ha, dif_pos hb]

lemma mssDMain_pos_neg (r : ℕ) {a : ℤ × ℤ} (ha : Enn a) (hb : ¬ Enn (a + vr r)) :
    mssDMain 𝕜 W r a = 0 := by
  rw [mssDMain, dif_pos ha, dif_neg hb]

lemma mssDMain_neg (r : ℕ) {a : ℤ × ℤ} (ha : ¬ Enn a) : mssDMain 𝕜 W r a = 0 := by
  rw [mssDMain, dif_neg ha]

/-- The differential `E_r^{a} → E_r^{b}` of the page, zero unless `b = a + (r, 1-r)`. -/
def mssD (r : ℕ) (a b : ℤ × ℤ) : mssE 𝕜 W r a ⟶ mssE 𝕜 W r b :=
  if h : b = a + vr r then
    mssDMain 𝕜 W r a ≫ eqToHom (congrArg (mssE 𝕜 W r) h.symm)
  else 0

lemma mssD_self (r : ℕ) (a : ℤ × ℤ) : mssD 𝕜 W r a (a + vr r) = mssDMain 𝕜 W r a := by
  rw [mssD, dif_pos rfl]
  rw [eqToHom_refl, Category.comp_id]

lemma mssD_shape (r : ℕ) (a b : ℤ × ℤ) (h : b ≠ a + vr r) : mssD 𝕜 W r a b = 0 := by
  rw [mssD, dif_neg h]

lemma mssDStep_comp (r : ℕ) {a : ℤ × ℤ} (h1 : EI a + r = EI (a + vr r))
    (h2 : EN a + 1 = EN (a + vr r)) (h3 : EI (a + vr r) + r = EI ((a + vr r) + vr r))
    (h4 : EN (a + vr r) + 1 = EN ((a + vr r) + vr r)) :
    mssDStep 𝕜 W r h1 h2 ≫ mssDStep 𝕜 W r h3 h4 = 0 := by
  simp only [mssDStep, Category.assoc]
  rw [← Category.assoc (pEcast 𝕜 W r h1 h2).hom (pD 𝕜 W r (EI (a + vr r)) (EN (a + vr r))) _]
  rw [← pD_pEcastNat 𝕜 W r (EI a + r) (EI (a + vr r)) (EN a + 1) (EN (a + vr r)) h1 h2
      (by rw [h1]) (by rw [h2])]
  rw [Category.assoc, ← Category.assoc]
  rw [pD_comp r (EI a) (EN a)]
  simp

lemma mssDMain_comp (r : ℕ) (a : ℤ × ℤ) :
    mssDMain 𝕜 W r a ≫ mssDMain 𝕜 W r (a + vr r) = 0 := by
  by_cases ha : Enn a
  · by_cases hb : Enn (a + vr r)
    · by_cases hc : Enn ((a + vr r) + vr r)
      · rw [mssDMain_pos 𝕜 W r ha hb, mssDMain_pos 𝕜 W r hb hc]
        exact mssDStep_comp 𝕜 W r (EI_add_vr r ha hb) (EN_add_vr r ha) (EI_add_vr r hb hc)
          (EN_add_vr r hb)
      · rw [mssDMain_pos 𝕜 W r ha hb, mssDMain_pos_neg 𝕜 W r hb hc, comp_zero]
    · rw [mssDMain_pos_neg 𝕜 W r ha hb, zero_comp]
  · rw [mssDMain_neg 𝕜 W r ha, zero_comp]

lemma mssD_comp (r : ℕ) (a b c : ℤ × ℤ) : mssD 𝕜 W r a b ≫ mssD 𝕜 W r b c = 0 := by
  by_cases hb : b = a + vr r
  · rw [hb]
    rw [mssD_self]
    by_cases hc : c = (a + vr r) + vr r
    · rw [hc, mssD_self]
      exact mssDMain_comp 𝕜 W r a
    · rw [mssD_shape 𝕜 W r (a + vr r) c hc, comp_zero]
  · rw [mssD_shape 𝕜 W r a b hb, zero_comp]


/-- Transport of a concrete page along equalities of both `ℕ`-indices. -/
def pCast (r : ℕ) {s s' n n' : ℕ} (h : s = s') (h' : n = n') :
    pEraw 𝕜 W r s n →ₗ[𝕜] pEraw 𝕜 W r s' n' :=
  (congrArg (fun u : ℕ × ℕ => pEraw 𝕜 W r u.1 u.2) (show (s, n) = (s', n') from by rw [h, h'])) ▸
    (LinearMap.id : pEraw 𝕜 W r s n →ₗ[𝕜] pEraw 𝕜 W r s n)

lemma pEcast_comp (r : ℕ) {s s' s'' n n' n'' : ℕ} (h1 : s = s') (h2 : s' = s'')
    (h1' : n = n') (h2' : n' = n'') :
    (pEcast 𝕜 W r h1 h1').hom ≫ (pEcast 𝕜 W r h2 h2').hom
      = (pEcast 𝕜 W r (h1.trans h2) (h1'.trans h2')).hom := by
  subst h1; subst h2; subst h1'; subst h2'
  rw [pEcast_hom_id]; simp

lemma pEcast_inv (r : ℕ) {s s' n n' : ℕ} (h : s = s') (h' : n = n') :
    (pEcast 𝕜 W r h h').hom ≫ (pEcast 𝕜 W r h.symm h'.symm).hom = 𝟙 (pEraw 𝕜 W r s n) := by
  subst h; subst h'; rw [pEcast_hom_id]; simp

lemma pd_mul_pEcast_apply (r s s' n n' S S' N N' : ℕ) (h1 : s = S) (h2 : n = N)
    (h3 : s' = S') (h4 : n' = N') (x : pEraw 𝕜 W r S N) (y : pEraw 𝕜 W r S' N') :
    (pEcast 𝕜 W r (by omega : s + s' = S + S') (by omega : n + n' = N + N')).hom
        ((pd_mul r s n s' n') ((pEcast 𝕜 W r h1.symm h2.symm).hom x)
          ((pEcast 𝕜 W r h3.symm h4.symm).hom y))
      = (pd_mul r S N S' N') x y := by
  subst h1; subst h2; subst h3; subst h4
  simp [pEcast_hom_id]

/-- The canonical identification of the bidegree-indexed page with the concrete page. -/
def mssNorm (r : ℕ) (s q : ℕ) : mssE 𝕜 W r ((s : ℤ), (q : ℤ)) ≅ pEraw 𝕜 W r s (s + q) :=
  pEcast 𝕜 W r (EI_pair s q) (EN_pair s q)

/-! ## 4. The product -/

/-- The product on covariant pages, on the honest part of the bidegree range. -/
def mssMulStep (r : ℕ) {a b : ℤ × ℤ} (ha : Enn a) (hb : Enn b) :
    mssE 𝕜 W r a →ₗ[𝕜] mssE 𝕜 W r b →ₗ[𝕜] mssE 𝕜 W r (a + b) :=
  (LinearMap.llcomp 𝕜 (mssE 𝕜 W r b) (pEraw 𝕜 W r (EI a + EI b) (EN a + EN b))
      (pEraw 𝕜 W r (EI (a + b)) (EN (a + b))) (pCast 𝕜 W r (EI_add ha hb) (EN_add ha hb))).comp
    (pd_mul r (EI a) (EN a) (EI b) (EN b))

/-- The product on the pages, zero off the first quadrant. -/
def mssMulRaw (r : ℕ) (a b : ℤ × ℤ) :
    mssE 𝕜 W r a →ₗ[𝕜] mssE 𝕜 W r b →ₗ[𝕜] mssE 𝕜 W r (a + b) :=
  if ha : 0 ≤ a.1 ∧ 0 ≤ a.2 then
    (if hb : 0 ≤ b.1 ∧ 0 ≤ b.2 then mssMulStep 𝕜 W r ha hb else 0)
  else 0

lemma mssMulRaw_pos (r : ℕ) {a b : ℤ × ℤ} (ha : Enn a) (hb : Enn b) :
    mssMulRaw 𝕜 W r a b = mssMulStep 𝕜 W r ha hb := by
  rw [mssMulRaw, dif_pos ha, dif_pos hb]

lemma mssMulRaw_neg (r : ℕ) {a b : ℤ × ℤ} (ha : ¬ Enn a) : mssMulRaw 𝕜 W r a b = 0 := by
  rw [mssMulRaw, dif_neg ha]

lemma mssMulRaw_neg' (r : ℕ) {a b : ℤ × ℤ} (ha : Enn a) (hb : ¬ Enn b) :
    mssMulRaw 𝕜 W r a b = 0 := by
  rw [mssMulRaw, dif_pos ha, dif_neg hb]

lemma pCast_apply_self (r : ℕ) {s n : ℕ} (x : pEraw 𝕜 W r s n) :
    pCast 𝕜 W r (rfl : s = s) (rfl : n = n) x = x := by
  simp [pCast]

/-- Transport of a page along an equality of bidegrees. -/
def mssCast (r : ℕ) {x y : ℤ × ℤ} (h : x = y) : mssE 𝕜 W r x →ₗ[𝕜] mssE 𝕜 W r y :=
  h ▸ (LinearMap.id : mssE 𝕜 W r x →ₗ[𝕜] mssE 𝕜 W r x)

theorem mssCast_rfl (r : ℕ) {x : ℤ × ℤ} :
    mssCast 𝕜 W r (rfl : x = x) = LinearMap.id := by
  simp [mssCast]

lemma mssCast_eq_pCast (r : ℕ) {a b : ℤ × ℤ} (h : a = b) :
    mssCast 𝕜 W r h = pCast 𝕜 W r (congrArg EI h) (congrArg EN h) := by
  cases h; rfl

/-- The product `E_r^a × E_r^b → E_r^c` of the pages (with the index cast `a + b = c`). -/
def mssMul (r : ℕ) (a b c : ℤ × ℤ) (h : a + b = c) :
    mssE 𝕜 W r a →ₗ[𝕜] mssE 𝕜 W r b →ₗ[𝕜] mssE 𝕜 W r c :=
  (LinearMap.llcomp 𝕜 (mssE 𝕜 W r b) (mssE 𝕜 W r (a + b)) (mssE 𝕜 W r c)
      (mssCast 𝕜 W r h)).comp (mssMulRaw 𝕜 W r a b)

lemma mssMul_congr (r : ℕ) (a b c : ℤ × ℤ) (h1 h2 : a + b = c)
    (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) :
    mssMul 𝕜 W r a b c h1 x y = mssMul 𝕜 W r a b c h2 x y := by
  have h : h1 = h2 := Subsingleton.elim _ _
  rw [h]

lemma mssMul_pos (r : ℕ) {a b c : ℤ × ℤ} (ha : Enn a) (hb : Enn b) (h : a + b = c) :
    mssMul 𝕜 W r a b c h
      = (LinearMap.llcomp 𝕜 (mssE 𝕜 W r b) (mssE 𝕜 W r (a + b)) (mssE 𝕜 W r c)
          (mssCast 𝕜 W r h)).comp (mssMulStep 𝕜 W r ha hb) := by
  rw [mssMul, mssMulRaw_pos 𝕜 W r ha hb]

/-! ## 5. The projection `ker d_r → E_{r+1}` -/

lemma pEcast_injective (r : ℕ) {s s' n n' : ℕ} (h : s = s') (h' : n = n') :
    Function.Injective (pEcast 𝕜 W r h h').hom := by
  intro x y hxy
  have h2 := congrArg (fun t => (pEcast 𝕜 W r h h').inv.hom t) hxy
  simpa using h2

lemma le_vr (r : ℕ) (hr : 2 ≤ r) {a : ℤ × ℤ} (ha : Enn a)
    (hb : ¬ Enn (a + vr r)) : EN a + 1 + 1 ≤ EI a + r := by
  rw [Enn_of_nonneg ha, EN_of_nonneg ha]
  have hlt : a.2 + 1 - (r : ℤ) < 0 := by
    by_contra h
    apply hb
    exact ⟨by rw [fst_add_vr]; linarith [ha.1, Int.natCast_nonneg r],
           by rw [snd_add_vr]; linarith⟩
  have h2 : a.2 ≤ (r : ℤ) - 2 := by omega
  have h3 : a.1 + a.2 ≤ a.1 + ((r:ℤ) - 2) := by linarith [ha.1]
  have h4 := Int.toNat_le_toNat h3
  have h5 : (a.1 + ((r:ℤ) - 2)).toNat = a.1.toNat + (r - 2) := by
    rw [Int.toNat_add ha.1 (by omega)]
    congr 1
    exact Int.toNat_sub r 2
  rw [h5] at h4
  omega

lemma le_not (r : ℕ) (hr : 2 ≤ r) {a : ℤ × ℤ} (ha : ¬ Enn a) : EN a + 1 + 1 ≤ EI a + r := by
  have h := EN_lt_EI_of_not ha
  omega

lemma pD_hom_eq_zero_of (r s n : ℕ) (h : n + 1 + 1 ≤ s + r) (x : pEraw 𝕜 W r s n) :
    (pD 𝕜 W r s n).hom x = 0 := by
  haveI : Subsingleton (pEraw 𝕜 W r (s + r) (n + 1)) :=
    subsingleton_pEraw_of 𝕜 W r (s + r) (n + 1) h
  exact Subsingleton.elim _ _

lemma mssProjAux_mem (r : ℕ) (hr : 2 ≤ r) (a : ℤ × ℤ)
    (x : ↥(LinearMap.ker (mssDMain 𝕜 W r a).hom)) :
    x.1 ∈ LinearMap.ker (pD 𝕜 W r (EI a) (EN a)).hom := by
  rw [LinearMap.mem_ker]
  by_cases ha : Enn a
  · by_cases hb : Enn (a + vr r)
    · have hx : (mssDStep 𝕜 W r (EI_add_vr r ha hb) (EN_add_vr r ha)).hom x.1 = 0 := by
        rw [← mssDMain_pos 𝕜 W r ha hb]; exact x.2
      rw [mssDStep] at hx
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx
      refine pEcast_injective 𝕜 W r (EI_add_vr r ha hb) (EN_add_vr r ha) ?_
      rw [hx, map_zero]
    · exact pD_hom_eq_zero_of 𝕜 W r (EI a) (EN a) (le_vr r hr ha hb) x.1
  · exact pD_hom_eq_zero_of 𝕜 W r (EI a) (EN a) (le_not r hr ha) x.1

/-- The projection of the concrete pages, transported to the bidegree indexing. -/
def mssProjAux (r : ℕ) (hr : 2 ≤ r) (a : ℤ × ℤ) :
    ↥(LinearMap.ker (mssDMain 𝕜 W r a).hom) →ₗ[𝕜] mssE 𝕜 W (r + 1) a :=
  { toFun := fun x => pd_proj 𝕜 W r (EI a) (EN a) ⟨x.1, mssProjAux_mem 𝕜 W r hr a x⟩
    map_add' := by
      intro x y
      have h : (⟨(x + y).1, mssProjAux_mem 𝕜 W r hr a (x + y)⟩ :
            ↥(LinearMap.ker (pD 𝕜 W r (EI a) (EN a)).hom))
          = ⟨x.1, mssProjAux_mem 𝕜 W r hr a x⟩ + ⟨y.1, mssProjAux_mem 𝕜 W r hr a y⟩ :=
        Subtype.ext rfl
      show pd_proj 𝕜 W r (EI a) (EN a) ⟨(x + y).1, _⟩ = _
      rw [h, map_add]
    map_smul' := by
      intro t x
      have h : (⟨(t • x).1, mssProjAux_mem 𝕜 W r hr a (t • x)⟩ :
            ↥(LinearMap.ker (pD 𝕜 W r (EI a) (EN a)).hom))
          = t • ⟨x.1, mssProjAux_mem 𝕜 W r hr a x⟩ :=
        Subtype.ext rfl
      show pd_proj 𝕜 W r (EI a) (EN a) ⟨(t • x).1, _⟩ = _
      rw [h, map_smul, RingHom.id_apply] }

/-- The inclusion of the cycles of `d_r` into the cycles of the underlying concrete differential. -/
def mssKerIncl (r : ℕ) (a : ℤ × ℤ) :
    ↥(LinearMap.ker (mssD 𝕜 W r a (a + vr r)).hom) →ₗ[𝕜]
      ↥(LinearMap.ker (mssDMain 𝕜 W r a).hom) :=
  { toFun := fun x => ⟨x.1, by rw [LinearMap.mem_ker, ← mssD_self]; exact x.2⟩
    map_add' := fun x y => Subtype.ext rfl
    map_smul' := fun t x => Subtype.ext rfl }

/-- The projection `ker d_r → E_{r+1}` (zero for `r < 2`, where it is unconstrained). -/
def mssProj (r : ℕ) (a : ℤ × ℤ) :
    ↥(LinearMap.ker (mssD 𝕜 W r a (a + vr r)).hom) →ₗ[𝕜] mssE 𝕜 W (r + 1) a :=
  if hr : 2 ≤ r then (mssProjAux 𝕜 W r hr a).comp (mssKerIncl 𝕜 W r a) else 0

lemma mssKerIncl_coe (r : ℕ) (a : ℤ × ℤ)
    (x : ↥(LinearMap.ker (mssD 𝕜 W r a (a + vr r)).hom)) :
    (mssKerIncl 𝕜 W r a x : mssE 𝕜 W r a) = x := rfl

lemma mssProj_apply (r : ℕ) (a : ℤ × ℤ) (hr : 2 ≤ r)
    (x : ↥(LinearMap.ker (mssD 𝕜 W r a (a + vr r)).hom)) :
    mssProj 𝕜 W r a x = mssProjAux 𝕜 W r hr a (mssKerIncl 𝕜 W r a x) := by
  rw [mssProj, dif_pos hr]; rfl

/-- A cycle of the concrete page is a cycle of the bidegree-indexed differential. -/
lemma mem_ker_mssDMain (r : ℕ) (a : ℤ × ℤ) {v : mssE 𝕜 W r a}
    (hv : v ∈ LinearMap.ker (pD 𝕜 W r (EI a) (EN a)).hom) :
    v ∈ LinearMap.ker (mssDMain 𝕜 W r a).hom := by
  rw [LinearMap.mem_ker] at hv ⊢
  by_cases ha : Enn a
  · by_cases hb : Enn (a + vr r)
    · rw [mssDMain_pos 𝕜 W r ha hb, mssDStep]
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hv, map_zero]
    · rw [mssDMain_pos_neg 𝕜 W r ha hb]; rfl
  · rw [mssDMain_neg 𝕜 W r ha]; rfl

/-- A cycle of the bidegree-indexed differential is a cycle of the concrete page. -/
lemma mem_ker_pD (r : ℕ) (a : ℤ × ℤ) {v : mssE 𝕜 W r a}
    (hv : v ∈ LinearMap.ker (mssDMain 𝕜 W r a).hom) :
    v ∈ LinearMap.ker (mssD 𝕜 W r a (a + vr r)).hom := by
  rw [LinearMap.mem_ker] at hv ⊢
  rw [mssD_self]
  exact hv

lemma mssProj_surj (r : ℕ) (a : ℤ × ℤ) (hr : 2 ≤ r) :
    Function.Surjective (mssProj 𝕜 W r a) := by
  intro y
  obtain ⟨w, hw⟩ := pd_proj_surj 𝕜 W r (EI a) (EN a) hr y
  refine ⟨⟨w.1, mem_ker_pD 𝕜 W r a (mem_ker_mssDMain 𝕜 W r a w.2)⟩, ?_⟩
  rw [mssProj_apply 𝕜 W r a hr]
  show pd_proj 𝕜 W r (EI a) (EN a) ⟨w.1, _⟩ = y
  rwa [show (⟨w.1, _⟩ : ↥(LinearMap.ker (pD 𝕜 W r (EI a) (EN a)).hom)) = w from Subtype.ext rfl]


/-! ## 6. The bottom row and the zeroth column -/

/-- The (linear) inclusion `E_r^a → ker d_r` when the differential out of `a` vanishes. -/
def mssTopIncl (r : ℕ) (a : ℤ × ℤ)
    (h : LinearMap.ker (mssD 𝕜 W r a (a + vr r)).hom = ⊤) :
    mssE 𝕜 W r a →ₗ[𝕜] ↥(LinearMap.ker (mssD 𝕜 W r a (a + vr r)).hom) :=
  (LinearEquiv.ofEq ⊤ (LinearMap.ker (mssD 𝕜 W r a (a + vr r)).hom) h.symm).toLinearMap.comp
    (Submodule.topEquiv (R := 𝕜) (M := mssE 𝕜 W r a)).symm.toLinearMap

lemma mssTopIncl_apply (r : ℕ) (a : ℤ × ℤ)
    (h : LinearMap.ker (mssD 𝕜 W r a (a + vr r)).hom = ⊤)
    (x : ↥(LinearMap.ker (mssD 𝕜 W r a (a + vr r)).hom)) :
    mssTopIncl 𝕜 W r a h (x : mssE 𝕜 W r a) = x :=
  Subtype.ext rfl

lemma ker_mssD_bot (r : ℕ) (hr : 2 ≤ r) (s : ℤ) :
    LinearMap.ker (mssD 𝕜 W r ((s : ℤ), (0 : ℤ)) (((s : ℤ), (0 : ℤ)) + vr r)).hom = ⊤ := by
  have hnot : ¬ Enn (((s : ℤ), (0 : ℤ)) + vr r) := by
    rintro ⟨h1, h2⟩
    rw [snd_add_vr] at h2
    omega
  rw [mssD_self]
  by_cases ha : Enn ((s : ℤ), (0 : ℤ))
  · rw [mssDMain_pos_neg 𝕜 W r ha hnot, ModuleCat.hom_zero, LinearMap.ker_zero]
  · rw [mssDMain_neg 𝕜 W r ha, ModuleCat.hom_zero, LinearMap.ker_zero]

/-- The bottom row: `E_r^{s,0} ↠ E_{r+1}^{s,0}`. -/
def mssBot (r : ℕ) (s : ℤ) :
    mssE 𝕜 W r ((s : ℤ), (0 : ℤ)) →ₗ[𝕜] mssE 𝕜 W (r + 1) ((s : ℤ), (0 : ℤ)) :=
  if hr : 2 ≤ r then
    (mssProj 𝕜 W r ((s : ℤ), (0 : ℤ))).comp
      (mssTopIncl 𝕜 W r ((s : ℤ), (0 : ℤ)) (ker_mssD_bot 𝕜 W r hr s))
  else 0

lemma mssBot_spec (r : ℕ) (s : ℤ) (hr : 2 ≤ r)
    (x : ↥(LinearMap.ker (mssD 𝕜 W r ((s : ℤ), (0 : ℤ)) (((s : ℤ), (0 : ℤ)) + vr r)).hom)) :
    mssBot 𝕜 W r s (x : mssE 𝕜 W r ((s : ℤ), (0 : ℤ))) =
      mssProj 𝕜 W r ((s : ℤ), (0 : ℤ)) x := by
  rw [mssBot, dif_pos hr]
  show mssProj 𝕜 W r ((s : ℤ), (0 : ℤ))
      (mssTopIncl 𝕜 W r ((s : ℤ), (0 : ℤ)) (ker_mssD_bot 𝕜 W r hr s) x) = _
  rw [mssTopIncl_apply]

lemma mssProj_inj_col (r : ℕ) (q : ℤ) (hr : 2 ≤ r) :
    Function.Injective (mssProj 𝕜 W r ((0 : ℤ), q)) := by
  by_cases hq : 0 ≤ q
  · have ha : Enn ((0 : ℤ), q) := ⟨le_refl 0, hq⟩
    have hEI : EI ((0 : ℤ), q) = 0 := by
      simp only [EI, if_pos ha, Int.toNat_zero]
    intro x y hxy
    have hxy' : mssProjAux 𝕜 W r hr ((0 : ℤ), q) (mssKerIncl 𝕜 W r ((0 : ℤ), q) x)
        = mssProjAux 𝕜 W r hr ((0 : ℤ), q) (mssKerIncl 𝕜 W r ((0 : ℤ), q) y) := by
      rw [← mssProj_apply 𝕜 W r ((0 : ℤ), q) hr x,
        ← mssProj_apply 𝕜 W r ((0 : ℤ), q) hr y]
      exact hxy
    change pd_proj 𝕜 W r (EI ((0 : ℤ), q)) (EN ((0 : ℤ), q))
        ⟨(mssKerIncl 𝕜 W r ((0 : ℤ), q) x).1, _⟩
      = pd_proj 𝕜 W r (EI ((0 : ℤ), q)) (EN ((0 : ℤ), q))
        ⟨(mssKerIncl 𝕜 W r ((0 : ℤ), q) y).1, _⟩ at hxy'
    have h2 := pd_proj_injective_low 𝕜 W r (EI ((0 : ℤ), q)) (EN ((0 : ℤ), q)) hr
      (by rw [hEI]; exact Nat.zero_lt_of_lt hr) hxy'
    have h3 : (x : mssE 𝕜 W r ((0 : ℤ), q)) = (y : mssE 𝕜 W r ((0 : ℤ), q)) := by
      have h4 := congrArg (fun t : ↥(LinearMap.ker
        (pD 𝕜 W r (EI ((0 : ℤ), q)) (EN ((0 : ℤ), q))).hom) =>
          (t : mssE 𝕜 W r ((0 : ℤ), q))) h2
      simpa [mssKerIncl_coe] using h4
    exact Subtype.ext h3
  · have hns : ¬ Enn ((0 : ℤ), q) := fun h => hq h.2
    haveI := subsingleton_mssE 𝕜 W r hns
    exact fun x y _ => Subsingleton.elim x y

/-- The projection `ker d_r → E_{r+1}` at the zeroth column, as a linear equivalence. -/
def mssProjEquiv (r : ℕ) (q : ℤ) (hr : 2 ≤ r) :
    mssE 𝕜 W (r + 1) ((0 : ℤ), q) ≃ₗ[𝕜]
      ↥(LinearMap.ker (mssD 𝕜 W r ((0 : ℤ), q) (((0 : ℤ), q) + vr r)).hom) :=
  (LinearEquiv.ofBijective (mssProj 𝕜 W r ((0 : ℤ), q))
    ⟨mssProj_inj_col 𝕜 W r q hr, mssProj_surj 𝕜 W r ((0 : ℤ), q) hr⟩).symm

/-- The zeroth column: `E_{r+1}^{0,q} ↪ E_r^{0,q}`. -/
def mssCol (r : ℕ) (q : ℤ) :
    mssE 𝕜 W (r + 1) ((0 : ℤ), q) →ₗ[𝕜] mssE 𝕜 W r ((0 : ℤ), q) :=
  if hr : 2 ≤ r then
    (Submodule.subtype (LinearMap.ker (mssD 𝕜 W r ((0 : ℤ), q)
      (((0 : ℤ), q) + vr r)).hom)).comp (mssProjEquiv 𝕜 W r q hr).toLinearMap
  else 0

lemma mssCol_spec (r : ℕ) (q : ℤ) (hr : 2 ≤ r)
    (x : ↥(LinearMap.ker (mssD 𝕜 W r ((0 : ℤ), q) (((0 : ℤ), q) + vr r)).hom)) :
    mssCol 𝕜 W r q (mssProj 𝕜 W r ((0 : ℤ), q) x) = x := by
  rw [mssCol, dif_pos hr]
  show Submodule.subtype _ ((mssProjEquiv 𝕜 W r q hr) (mssProj 𝕜 W r ((0 : ℤ), q) x)) = x
  rw [show (mssProjEquiv 𝕜 W r q hr) (mssProj 𝕜 W r ((0 : ℤ), q) x) = x from
    LinearEquiv.symm_apply_apply _ x]
  rfl

end
end Work.Pi6.MSS
