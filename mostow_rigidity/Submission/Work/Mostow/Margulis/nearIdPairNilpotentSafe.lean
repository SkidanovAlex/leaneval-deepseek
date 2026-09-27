import Mathlib
import Submission.Work.Mostow.margulisPairDefs
import Submission.Work.Mostow.Margulis.commSeqBase
import Submission.Work.Mostow.nilpotentOfSimpleComm

/-!
# Two near-identity elements of a discrete subgroup of `PO(n,1)` generate a nilpotent group (safe copy)

The Margulis lemma, in its simplest form: if `γ, δ` are elements of a discrete subgroup
`Γ ≤ PO(n,1)` that are entrywise close to the identity matrix (`NearId q`, with
`8 (n+1)^3 q ≤ 1/2`), then `⟨γ, δ⟩ ≤ PO(n,1)` is nilpotent.

The proof is the classical Zassenhaus argument, done entirely with the entrywise matrix
estimates already available in `Submission.Work.Mostow.Margulis.nearId_pair_commuting`:

* `near1_commutator_gen` shows that the commutator of two matrices with defects `a`, `b` has
  defect at most `2 (n+1)^3 a b (1+a) (1+b)`;
* consequently, the canonical lift of every *left-normed simple commutator* of weight `k` in
  `γ, δ` has entrywise defect at most `q (1/2)^k` (`liftsT_near`);
* the discreteness gap (`discrete_gap`) says that no element of `Γ` except the identity has a
  representative of defect `< r`, for some `r > 0`;
* so for `k` with `q (1/2)^k < r` every simple commutator of weight `k` in `γ, δ` is trivial,
  and `nilpotentOfSimpleComm` turns this into nilpotency of `⟨γ, δ⟩`.
-/

open scoped commutatorElement

namespace Work.Mostow.Margulis

open Work.Mostow
open Work.Mostow.Margulis.Snap

variable {n : ℕ}

/-- The set of matrices built from `A`, `B` by left-normed iterated commutators of weight `k`
(`SnLifts A B 0 = {A, B}`, `SnLifts A B (k+1) = {y * z * y⁻¹ * z⁻¹ | y ∈ SnLifts A B k, z ∈ SnLifts A B 0}`). -/
def SnLifts (A B : Submission.Mostow.O1 n) : ℕ → Set (Submission.Mostow.O1 n)
  | 0 => {A, B}
  | (k + 1) => {w | ∃ y ∈ SnLifts A B k, ∃ z ∈ SnLifts A B 0, w = y * z * y⁻¹ * z⁻¹}

lemma snLifts_zero (A B : Submission.Mostow.O1 n) :
    SnLifts A B 0 = ({A, B} : Set (Submission.Mostow.O1 n)) := by
  simp only [SnLifts]

lemma mem_snLifts_succ (A B : Submission.Mostow.O1 n) (k : ℕ) (w : Submission.Mostow.O1 n) :
    w ∈ SnLifts A B (k + 1) ↔
      ∃ y ∈ SnLifts A B k, ∃ z ∈ SnLifts A B 0, w = y * z * y⁻¹ * z⁻¹ := by
  simp only [SnLifts, Set.mem_setOf_eq]

/-- The commutator defect bound of `near1_commutator_gen`, in the form in which we use it:
for defects `a ≤ q`, the defect of `[A, B]` is at most `a / 2` once `8 (n+1)^3 q ≤ 1/2`. -/
lemma sn_commutator_bound (a q : ℝ) (ha : 0 ≤ a) (haq : a ≤ q) (hq : 0 < q)
    (hsmall : 8 * (msz n) ^ 3 * q ≤ 1 / 2) :
    2 * (msz n) ^ 3 * a * q * (1 + a) * (1 + q) ≤ a * (1 / 2) := by
  have hm1 : (1 : ℝ) ≤ msz n := one_le_msz n
  have hm3 : (1 : ℝ) ≤ (msz n) ^ 3 := one_le_pow₀ hm1
  have hq1 : q ≤ 1 := by nlinarith
  have h1 : (1 + a) * (1 + q) ≤ 4 := by nlinarith
  have h2 : 0 ≤ 2 * (msz n) ^ 3 * a * q := by positivity
  calc 2 * (msz n) ^ 3 * a * q * (1 + a) * (1 + q)
      = (2 * (msz n) ^ 3 * a * q) * ((1 + a) * (1 + q)) := by ring
    _ ≤ (2 * (msz n) ^ 3 * a * q) * 4 := mul_le_mul_of_nonneg_left h1 h2
    _ = (8 * (msz n) ^ 3 * q) * a := by ring
    _ ≤ (1 / 2) * a := mul_le_mul_of_nonneg_right hsmall ha
    _ = a * (1 / 2) := by ring

/-- The defect of the canonical lift of a simple commutator of weight `k` is at most `q (1/2)^k`. -/
lemma snLifts_near {A B : Submission.Mostow.O1 n} {q : ℝ} (hA : Near1 A q) (hB : Near1 B q)
    (hq : 0 < q) (hsmall : 8 * (msz n) ^ 3 * q ≤ 1 / 2) :
    ∀ k : ℕ, ∀ w ∈ SnLifts A B k, Near1 w (q * (1 / 2) ^ k) := by
  intro k
  induction k with
  | zero =>
    intro w hw
    rw [snLifts_zero] at hw
    rcases hw with hw | hw
    · rw [hw]; simpa using hA
    · rw [hw]; simpa using hB
  | succ k ih =>
    intro w hw
    rw [mem_snLifts_succ] at hw
    obtain ⟨y, hy, z, hz, rfl⟩ := hw
    rw [snLifts_zero] at hz
    have hy' : Near1 y (q * (1 / 2) ^ k) := ih y hy
    have hz' : Near1 z q := by
      rcases hz with hz | hz
      · rw [hz]; exact hA
      · rw [hz]; exact hB
    refine near1_mono (near1_commutator_gen hy' hz') ?_
    have ha : (0 : ℝ) ≤ q * (1 / 2) ^ k := by positivity
    have haq : q * (1 / 2) ^ k ≤ q := by
      have h : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith [hq, h]
    have hb := sn_commutator_bound (n := n) (q * (1 / 2) ^ k) q ha haq hq hsmall
    rwa [show q * (1 / 2) ^ k * (1 / 2) = q * (1 / 2) ^ (k + 1) from by
      rw [pow_succ]; ring] at hb

/-- Every element of `SnLifts A B 0` maps to an element of `{γ, δ}`. -/
lemma snLifts_surj_zero {γ δ : LeanEval.Geometry.MostowRigidity.PO n 1}
    {A B : Submission.Mostow.O1 n}
    (hAeq : (A : LeanEval.Geometry.MostowRigidity.PO n 1) = γ)
    (hBeq : (B : LeanEval.Geometry.MostowRigidity.PO n 1) = δ) :
    ∀ c ∈ ({γ, δ} : Set (LeanEval.Geometry.MostowRigidity.PO n 1)),
      ∃ w ∈ SnLifts A B 0, (w : LeanEval.Geometry.MostowRigidity.PO n 1) = c := by
  intro c hc
  rw [snLifts_zero]
  rcases hc with hc | hc
  · exact ⟨A, Set.mem_insert _ _, by rw [hAeq, hc]⟩
  · exact ⟨B, Set.mem_insert_of_mem _ rfl, by rw [hBeq, hc]⟩

/-- Every simple commutator of weight `k` in `γ, δ` is the image of an element of `SnLifts A B k`. -/
lemma snLifts_surj {γ δ : LeanEval.Geometry.MostowRigidity.PO n 1}
    {A B : Submission.Mostow.O1 n}
    (hAeq : (A : LeanEval.Geometry.MostowRigidity.PO n 1) = γ)
    (hBeq : (B : LeanEval.Geometry.MostowRigidity.PO n 1) = δ) :
    ∀ k : ℕ, ∀ c ∈ SimpleCommSet ({γ, δ} : Set (LeanEval.Geometry.MostowRigidity.PO n 1)) k,
      ∃ w ∈ SnLifts A B k, (w : LeanEval.Geometry.MostowRigidity.PO n 1) = c := by
  intro k
  induction k with
  | zero => simpa only [SimpleCommSet_zero] using snLifts_surj_zero hAeq hBeq
  | succ k ih =>
    intro c hc
    rw [mem_SimpleCommSet_succ] at hc
    obtain ⟨a, ha, x, hx, rfl⟩ := hc
    obtain ⟨y, hy, hyc⟩ := ih a ha
    obtain ⟨z, hz, hzc⟩ := snLifts_surj_zero hAeq hBeq x hx
    refine ⟨y * z * y⁻¹ * z⁻¹, ?_, ?_⟩
    · rw [mem_snLifts_succ]; exact ⟨y, hy, z, hz, rfl⟩
    · have hcoe : ((y * z * y⁻¹ * z⁻¹ : Submission.Mostow.O1 n)
          : LeanEval.Geometry.MostowRigidity.PO n 1)
          = (y : LeanEval.Geometry.MostowRigidity.PO n 1) * (z : LeanEval.Geometry.MostowRigidity.PO n 1)
            * (y : LeanEval.Geometry.MostowRigidity.PO n 1)⁻¹
            * (z : LeanEval.Geometry.MostowRigidity.PO n 1)⁻¹ := rfl
      rw [hcoe, hyc, hzc]
      rfl

theorem nilpotent_of_nearId_pair (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Γ)) (γ δ : Γ) (q : ℝ) (hq : 0 < q)
    (hsmall : 8 * (Work.Mostow.msz n) ^ 3 * q ≤ 1 / 2)
    (hγ : Work.Mostow.NearId q (γ : LeanEval.Geometry.MostowRigidity.PO n 1))
    (hδ : Work.Mostow.NearId q (δ : LeanEval.Geometry.MostowRigidity.PO n 1)) :
    Group.IsNilpotent (Subgroup.closure ({((γ : LeanEval.Geometry.MostowRigidity.PO n 1)),
      ((δ : LeanEval.Geometry.MostowRigidity.PO n 1))} : Set (LeanEval.Geometry.MostowRigidity.PO n 1))) := by
  obtain ⟨A, hAeq, hAnear⟩ := hγ
  obtain ⟨B, hBeq, hBnear⟩ := hδ
  obtain ⟨r, hrpos, -, hgap⟩ := discrete_gap n hA Γ hdisc
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < r / q by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hNq : q * (1 / 2) ^ N < r := by
    have h1 := mul_lt_mul_of_pos_left hN hq
    have h2 : q * (r / q) = r := by field_simp
    rwa [h2] at h1
  have hXsub : ({((γ : LeanEval.Geometry.MostowRigidity.PO n 1)),
      ((δ : LeanEval.Geometry.MostowRigidity.PO n 1))} : Set (LeanEval.Geometry.MostowRigidity.PO n 1)) ⊆ Γ := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact γ.2
    · exact δ.2
  have hle : Subgroup.closure ({((γ : LeanEval.Geometry.MostowRigidity.PO n 1)),
      ((δ : LeanEval.Geometry.MostowRigidity.PO n 1))} : Set (LeanEval.Geometry.MostowRigidity.PO n 1)) ≤ Γ :=
    (Subgroup.closure_le _).mpr hXsub
  refine nilpotentOfSimpleComm
    ({((γ : LeanEval.Geometry.MostowRigidity.PO n 1)),
      ((δ : LeanEval.Geometry.MostowRigidity.PO n 1))} : Set (LeanEval.Geometry.MostowRigidity.PO n 1)) N ?_
  intro k hk c hc
  obtain ⟨w, hw, hwc⟩ := snLifts_surj hAeq hBeq k c hc
  have hwΓ : (w : LeanEval.Geometry.MostowRigidity.PO n 1) ∈ Γ :=
    hle (by rw [hwc]; exact SimpleCommSet_subset_closure _ k hc)
  have hwnear : Near1 w (q * (1 / 2) ^ k) := snLifts_near hAnear hBnear hq hsmall k w hw
  have hkle : (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have hbnd : q * (1 / 2) ^ k ≤ q * (1 / 2) ^ N :=
    mul_le_mul_of_nonneg_left hkle (le_of_lt hq)
  have hwr : Near1 w r := near1_mono hwnear (le_of_lt (lt_of_le_of_lt hbnd hNq))
  have hw1 : w = 1 := hgap w hwΓ hwr
  rw [← hwc, hw1]
  rfl

end Work.Mostow.Margulis
