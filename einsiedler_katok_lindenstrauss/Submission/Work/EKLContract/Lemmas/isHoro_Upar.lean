import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.isHoro_Uij

/-!
# `U_(ab)` is an admissible (horospherical) subgroup

`U_(ab) = ⟨U_ab, U_ac, U_cb⟩` (`c` the third index, `hab`, `hac`, `hcb` the pairwise
inequalities) is the horospherical subgroup of EKL §4 for which the leafwise-measure
theory of `P_Leafwise` is used.  We verify `Work.EKLContract.IsHoro (Upar hab hac hcb)`:

* the carrier is the set of "upper unitriangular" matrices in the ordering `(a, c, b)`,
  hence closed in `SL₃(ℝ)`;
* the diagonal group `A = {aDiag t}` normalises it;
* it is contracted by `aDiag t` for any `t` with `t a < t c < t b`.

The proofs are explicit `3 × 3` matrix bookkeeping on top of
`Work.EKLContract.Lemmas.horoUij_*` from `isHoro_Uij.lean`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLContract.Lemmas

open Work.EKLContract

variable {a b c : Fin 3}

/-! ## A covering fact for three distinct elements of `Fin 3` -/

/-- Any three elements `a`, `b`, `c` of `Fin 3` which are pairwise distinct exhaust `Fin 3`. -/
lemma fin3_cover (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    ∀ k : Fin 3, k = a ∨ k = b ∨ k = c := by
  have hinj : Function.Injective (fun i : Fin 3 => ![a, b, c] i) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  intro k
  obtain ⟨i, hi⟩ := (Finite.surjective_of_injective hinj) k
  fin_cases i <;> simp_all

/-! ## The shape matrices of `U_(ab)` -/

/-- The matrix `1 + q E_{ac} + r E_{cb} + s E_{ab}`: the general element of `U_(ab)` in the
coordinates `(a, c, b)`. -/
def shapeMat (a b c : Fin 3) (q r s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 + Matrix.single a c q + Matrix.single c b r + Matrix.single a b s

lemma shapeMat_zero (a b c : Fin 3) : shapeMat a b c 0 0 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  simp [shapeMat]

lemma shapeMat_mul (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (q r s q' r' s' : ℝ) :
    shapeMat a b c q r s * shapeMat a b c q' r' s' =
      shapeMat a b c (q + q') (r + r') (s + s' + q * r') := by
  unfold shapeMat
  simp only [add_mul, mul_add, one_mul, mul_one]
  rw [Matrix.single_mul_single_of_ne (c:=q) (i:=a) (j:=c) (k:=a) hac.symm (d:=q'),
      Matrix.single_mul_single_of_ne (c:=q) (i:=a) (j:=c) (k:=a) hac.symm (d:=s'),
      Matrix.single_mul_single_of_ne (c:=r) (i:=c) (j:=b) (k:=a) (Ne.symm hab) (d:=q'),
      Matrix.single_mul_single_of_ne (c:=r) (i:=c) (j:=b) (k:=c) hcb.symm (d:=r'),
      Matrix.single_mul_single_of_ne (c:=r) (i:=c) (j:=b) (k:=a) (Ne.symm hab) (d:=s'),
      Matrix.single_mul_single_of_ne (c:=s) (i:=a) (j:=b) (k:=a) (Ne.symm hab) (d:=q'),
      Matrix.single_mul_single_of_ne (c:=s) (i:=a) (j:=b) (k:=c) hcb.symm (d:=r'),
      Matrix.single_mul_single_of_ne (c:=s) (i:=a) (j:=b) (k:=a) (Ne.symm hab) (d:=s'),
      Matrix.single_mul_single_same (c:=q) (i:=a) (j:=c) (k:=b) (d:=r')]
  simp only [Matrix.single_add]
  abel

/-! ## The parametrisation `(p,q,r) ↦ u_ac(q) u_cb(r) u_ab(p)` -/

/-- The shape element `u_ac(q) · u_cb(r) · u_ab(p)` of `U_(ab)`. -/
def uparShape (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (p q r : ℝ) : SL3 :=
  uij hac q * uij hcb r * uij hab p

lemma toMat_uparShape (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (p q r : ℝ) :
    toMat (uparShape hab hac hcb p q r) = shapeMat a b c q r (p + q * r) := by
  unfold uparShape shapeMat
  rw [toMat_mul, toMat_mul, horoUij_toMat, horoUij_toMat, horoUij_toMat]
  simp only [add_mul, mul_add, one_mul, mul_one]
  rw [Matrix.single_mul_single_same (c:=q) (i:=a) (j:=c) (k:=b) (d:=r),
      Matrix.single_mul_single_of_ne (c:=r) (i:=c) (j:=b) (k:=a) (Ne.symm hab) (d:=p),
      Matrix.single_mul_single_of_ne (c:=q) (i:=a) (j:=c) (k:=a) hac.symm (d:=p),
      Matrix.single_mul_single_of_ne (c:=q*r) (i:=a) (j:=b) (k:=a) (Ne.symm hab) (d:=p)]
  simp only [Matrix.single_add]
  abel

lemma uparShape_zero (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    uparShape hab hac hcb 0 0 0 = (1 : SL3) := by
  simp [uparShape, horoUij_zero]

lemma uparShape_mul (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (p q r p' q' r' : ℝ) :
    uparShape hab hac hcb p q r * uparShape hab hac hcb p' q' r' =
      uparShape hab hac hcb (p + p' - q' * r) (q + q') (r + r') := by
  apply ext_toMat
  rw [toMat_mul, toMat_uparShape, toMat_uparShape, toMat_uparShape, shapeMat_mul hab hac hcb]
  rw [show (p + q * r) + (p' + q' * r') + q * r' = (p + p' - q' * r) + (q + q') * (r + r')
      from by ring]

lemma uparShape_inv (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (p q r : ℝ) :
    (uparShape hab hac hcb p q r)⁻¹ = uparShape hab hac hcb (-p - q * r) (-q) (-r) := by
  have h : uparShape hab hac hcb p q r * uparShape hab hac hcb (-p - q * r) (-q) (-r)
      = (1 : SL3) := by
    rw [uparShape_mul]
    ring_nf
    exact uparShape_zero hab hac hcb
  exact inv_eq_of_mul_eq_one_right h

/-- The subgroup `{u_ac(q) u_cb(r) u_ab(p)} = U_(ab)`. -/
def uparShapeSub (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) : Subgroup SL3 where
  carrier := Set.range (fun t : ℝ × ℝ × ℝ => uparShape hab hac hcb t.1 t.2.1 t.2.2)
  one_mem' := ⟨(0, 0, 0), uparShape_zero hab hac hcb⟩
  mul_mem' := by
    rintro x y ⟨⟨p, q, r⟩, rfl⟩ ⟨⟨p', q', r'⟩, rfl⟩
    refine ⟨(p + p' - q' * r, q + q', r + r'), ?_⟩
    show uparShape hab hac hcb (p + p' - q' * r) (q + q') (r + r') =
      uparShape hab hac hcb p q r * uparShape hab hac hcb p' q' r'
    exact (uparShape_mul hab hac hcb p q r p' q' r').symm
  inv_mem' := by
    rintro x ⟨⟨p, q, r⟩, rfl⟩
    refine ⟨(-p - q * r, -q, -r), ?_⟩
    show uparShape hab hac hcb (-p - q * r) (-q) (-r) = (uparShape hab hac hcb p q r)⁻¹
    exact (uparShape_inv hab hac hcb p q r).symm

lemma mem_uparShapeSub (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (g : SL3) :
    g ∈ uparShapeSub hab hac hcb ↔ ∃ p q r : ℝ, uparShape hab hac hcb p q r = g := by
  constructor
  · rintro ⟨⟨p, q, r⟩, h⟩; exact ⟨p, q, r, h⟩
  · rintro ⟨p, q, r, h⟩; exact ⟨(p, q, r), h⟩

lemma Upar_eq_uparShapeSub (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    Upar hab hac hcb = uparShapeSub hab hac hcb := by
  apply le_antisymm
  · rw [Upar]
    refine sup_le (sup_le ?_ ?_) ?_
    · apply (Subgroup.closure_le (uparShapeSub hab hac hcb)).mpr
      rintro x ⟨s, rfl⟩
      exact (mem_uparShapeSub hab hac hcb _).mpr ⟨s, 0, 0, by simp [uparShape, horoUij_zero]⟩
    · apply (Subgroup.closure_le (uparShapeSub hab hac hcb)).mpr
      rintro x ⟨s, rfl⟩
      exact (mem_uparShapeSub hab hac hcb _).mpr ⟨0, s, 0, by simp [uparShape, horoUij_zero]⟩
    · apply (Subgroup.closure_le (uparShapeSub hab hac hcb)).mpr
      rintro x ⟨s, rfl⟩
      exact (mem_uparShapeSub hab hac hcb _).mpr ⟨0, 0, s, by simp [uparShape, horoUij_zero]⟩
  · intro x hx
    rw [mem_uparShapeSub] at hx
    obtain ⟨p, q, r, rfl⟩ := hx
    unfold uparShape
    refine mul_mem (mul_mem ?_ ?_) ?_
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨q, rfl⟩))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨r, rfl⟩)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨p, rfl⟩))

/-! ## Closedness: the carrier is a finite intersection of closed entry conditions -/

/-- The carrier of `U_(ab)` as a set of `SL₃(ℝ)`-elements with prescribed entries. -/
def uparSet (a b c : Fin 3) : Set SL3 :=
  {g | toMat g c a = 0 ∧ toMat g b a = 0 ∧ toMat g b c = 0 ∧
       toMat g a a = 1 ∧ toMat g c c = 1 ∧ toMat g b b = 1}

lemma continuous_toMat_entry (i j : Fin 3) : Continuous (fun g : SL3 => toMat g i j) :=
  (continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply _ continuous_id i)

lemma isClosed_uparSet (a b c : Fin 3) : IsClosed (uparSet a b c) := by
  have key : uparSet a b c = {g : SL3 | toMat g c a = 0} ∩ {g : SL3 | toMat g b a = 0} ∩
      {g : SL3 | toMat g b c = 0} ∩ {g : SL3 | toMat g a a = 1} ∩ {g : SL3 | toMat g c c = 1} ∩
      {g : SL3 | toMat g b b = 1} := by
    ext g
    simp only [uparSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [key]
  refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_) ?_) ?_
  all_goals exact isClosed_eq (continuous_toMat_entry _ _) continuous_const

/-- An element with the six prescribed entries of `U_(ab)` is exactly a shape. -/
lemma toMat_eq_shapeMat (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (g : SL3)
    (h1 : toMat g c a = 0) (h2 : toMat g b a = 0) (h3 : toMat g b c = 0)
    (h4 : toMat g a a = 1) (h5 : toMat g c c = 1) (h6 : toMat g b b = 1) :
    toMat g = shapeMat a b c (toMat g a c) (toMat g c b) (toMat g a b) := by
  apply Matrix.ext
  intro k l
  have hk := fin3_cover hab hac hcb k
  have hl := fin3_cover hab hac hcb l
  rcases hk with hk | hk | hk <;> subst hk <;>
    rcases hl with hl | hl | hl <;> subst hl <;>
    simp_all [shapeMat, Ne.symm hac, Ne.symm hab, Ne.symm hcb]

lemma uparShapeSub_coe_eq_uparSet (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    ((uparShapeSub hab hac hcb : Subgroup SL3) : Set SL3) = uparSet a b c := by
  ext g
  change g ∈ uparShapeSub hab hac hcb ↔ g ∈ uparSet a b c
  rw [mem_uparShapeSub]
  constructor
  · rintro ⟨p, q, r, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [toMat_uparShape] <;>
      simp_all [shapeMat, Ne.symm hac, Ne.symm hab, Ne.symm hcb]
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨toMat g a b - toMat g a c * toMat g c b, toMat g a c, toMat g c b, ?_⟩
    apply ext_toMat
    rw [toMat_uparShape]
    rw [show toMat g a b - toMat g a c * toMat g c b + toMat g a c * toMat g c b = toMat g a b
        from by ring]
    exact (toMat_eq_shapeMat hab hac hcb g h1 h2 h3 h4 h5 h6).symm

lemma isClosed_Upar (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    IsClosed ((Upar hab hac hcb : Subgroup SL3) : Set SL3) := by
  rw [Upar_eq_uparShapeSub, uparShapeSub_coe_eq_uparSet]
  exact isClosed_uparSet a b c

/-! ## Normalisation by the diagonal group -/

lemma aDiag_conj_uparShape (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (t : Fin 3 → ℝ) (p q r : ℝ) :
    aDiag t * uparShape hab hac hcb p q r * (aDiag t)⁻¹ =
      uparShape hab hac hcb (p * Real.exp (t a - t b)) (q * Real.exp (t a - t c))
        (r * Real.exp (t c - t b)) := by
  unfold uparShape
  rw [show aDiag t * (uij hac q * uij hcb r * uij hab p) * (aDiag t)⁻¹ =
      (aDiag t * uij hac q * (aDiag t)⁻¹) * (aDiag t * uij hcb r * (aDiag t)⁻¹) *
        (aDiag t * uij hab p * (aDiag t)⁻¹) from by group]
  simp only [horoUij_aDiag_conj]
  rw [mul_comm (Real.exp (t a - t c)) q, mul_comm (Real.exp (t c - t b)) r,
      mul_comm (Real.exp (t a - t b)) p]

lemma aDiag_conj_mem_Upar (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (t : Fin 3 → ℝ) (u : SL3) (hu : u ∈ Upar hab hac hcb) :
    aDiag t * u * (aDiag t)⁻¹ ∈ Upar hab hac hcb := by
  rw [Upar_eq_uparShapeSub] at hu ⊢
  rw [mem_uparShapeSub] at hu ⊢
  obtain ⟨p, q, r, rfl⟩ := hu
  exact ⟨p * Real.exp (t a - t b), q * Real.exp (t a - t c), r * Real.exp (t c - t b),
    (aDiag_conj_uparShape hab hac hcb t p q r).symm⟩

/-! ## Contraction -/

/-- The exponent vector `(0, 1, 2)` on `(a, c, b)`: contracts all three root groups of
`U_(ab)`. -/
def contractExp (a b c : Fin 3) : Fin 3 → ℝ := fun k => if k = b then 2 else if k = c then 1 else 0

lemma contractExp_a (hab : a ≠ b) (hac : a ≠ c) : contractExp a b c a = 0 := by
  simp only [contractExp, if_neg hab, if_neg hac]

lemma contractExp_b (a b c : Fin 3) : contractExp a b c b = 2 := by
  simp [contractExp]

lemma contractExp_c (hcb : c ≠ b) : contractExp a b c c = 1 := by
  simp [contractExp, hcb]

/-- The conjugated diagonal power of a shape element, with the explicit scalar factors. -/
lemma aDiag_pow_conj_uparShape (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (t : Fin 3 → ℝ) (n : ℕ) (p q r : ℝ) :
    aDiag t ^ n * uparShape hab hac hcb p q r * (aDiag t ^ n)⁻¹ =
      uparShape hab hac hcb (p * Real.exp ((n : ℝ) * (t a - t b)))
        (q * Real.exp ((n : ℝ) * (t a - t c))) (r * Real.exp ((n : ℝ) * (t c - t b))) := by
  rw [horoUij_aDiag_pow t n, aDiag_conj_uparShape]
  rw [show Real.exp ((fun k : Fin 3 => (n : ℝ) * t k) a - (fun k : Fin 3 => (n : ℝ) * t k) b)
        = Real.exp ((n : ℝ) * (t a - t b)) from congrArg Real.exp (by ring),
      show Real.exp ((fun k : Fin 3 => (n : ℝ) * t k) a - (fun k : Fin 3 => (n : ℝ) * t k) c)
        = Real.exp ((n : ℝ) * (t a - t c)) from congrArg Real.exp (by ring),
      show Real.exp ((fun k : Fin 3 => (n : ℝ) * t k) c - (fun k : Fin 3 => (n : ℝ) * t k) b)
        = Real.exp ((n : ℝ) * (t c - t b)) from congrArg Real.exp (by ring)]

/-- `Real.exp (n x) → 0` for `x < 0`. -/
lemma tendsto_exp_nat_mul_of_neg {x : ℝ} (hx : x < 0) :
    Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * x)) atTop (𝓝 0) := by
  have h1 : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hx
  have h0 : 0 ≤ Real.exp x := Real.exp_nonneg x
  have hp : Tendsto (fun n : ℕ => Real.exp x ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  simpa only [Real.exp_nat_mul] using hp

lemma tendsto_uij_comp_zero {i j : Fin 3} (h : i ≠ j) {g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => uij h (g n)) atTop (𝓝 1) := by
  have hc := ((horoUij_cont h).tendsto 0).comp hg
  rw [horoUij_zero h] at hc
  rwa [show ((fun s : ℝ => uij h s) ∘ g) = (fun n => uij h (g n)) from by funext n; rfl] at hc

lemma upar_contraction (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    ∀ u ∈ Upar hab hac hcb,
      Tendsto (fun n : ℕ => aDiag (contractExp a b c) ^ n * u * (aDiag (contractExp a b c) ^ n)⁻¹)
        atTop (𝓝 1) := by
  intro u hu
  rw [Upar_eq_uparShapeSub, mem_uparShapeSub] at hu
  obtain ⟨p, q, r, rfl⟩ := hu
  set te := contractExp a b c with hte
  have hta : te a = 0 := by rw [hte]; exact contractExp_a hab hac
  have htb : te b = 2 := by rw [hte]; exact contractExp_b a b c
  have htc : te c = 1 := by rw [hte]; exact contractExp_c hcb
  have hx1 : te a - te b < 0 := by rw [hta, htb]; norm_num
  have hx2 : te a - te c < 0 := by rw [hta, htc]; norm_num
  have hx3 : te c - te b < 0 := by rw [htc, htb]; norm_num
  have e1 : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (te a - te b))) atTop (𝓝 0) :=
    tendsto_exp_nat_mul_of_neg hx1
  have e2 : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (te a - te c))) atTop (𝓝 0) :=
    tendsto_exp_nat_mul_of_neg hx2
  have e3 : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (te c - te b))) atTop (𝓝 0) :=
    tendsto_exp_nat_mul_of_neg hx3
  have h1 : Tendsto (fun n : ℕ => p * Real.exp ((n : ℝ) * (te a - te b))) atTop (𝓝 0) := by
    simpa using e1.const_mul p
  have h2 : Tendsto (fun n : ℕ => q * Real.exp ((n : ℝ) * (te a - te c))) atTop (𝓝 0) := by
    simpa using e2.const_mul q
  have h3 : Tendsto (fun n : ℕ => r * Real.exp ((n : ℝ) * (te c - te b))) atTop (𝓝 0) := by
    simpa using e3.const_mul r
  have hfin : Tendsto
      (fun n : ℕ => uparShape hab hac hcb (p * Real.exp ((n : ℝ) * (te a - te b)))
        (q * Real.exp ((n : ℝ) * (te a - te c))) (r * Real.exp ((n : ℝ) * (te c - te b))))
      atTop (𝓝 1) := by
    have hA : Tendsto (fun n : ℕ => uij hac (q * Real.exp ((n : ℝ) * (te a - te c)))) atTop (𝓝 1) :=
      tendsto_uij_comp_zero hac h2
    have hB : Tendsto (fun n : ℕ => uij hcb (r * Real.exp ((n : ℝ) * (te c - te b)))) atTop (𝓝 1) :=
      tendsto_uij_comp_zero hcb h3
    have hC : Tendsto (fun n : ℕ => uij hab (p * Real.exp ((n : ℝ) * (te a - te b)))) atTop (𝓝 1) :=
      tendsto_uij_comp_zero hab h1
    have hprod := (hA.mul hB).mul hC
    rw [show (fun n : ℕ => uparShape hab hac hcb (p * Real.exp ((n : ℝ) * (te a - te b)))
        (q * Real.exp ((n : ℝ) * (te a - te c))) (r * Real.exp ((n : ℝ) * (te c - te b))))
        = (fun n : ℕ => (uij hac (q * Real.exp ((n : ℝ) * (te a - te c))) *
            uij hcb (r * Real.exp ((n : ℝ) * (te c - te b)))) *
            uij hab (p * Real.exp ((n : ℝ) * (te a - te b)))) from by funext n; rfl]
    simpa using hprod
  have heq : (fun n : ℕ => aDiag te ^ n * uparShape hab hac hcb p q r * (aDiag te ^ n)⁻¹)
      = fun n : ℕ => uparShape hab hac hcb (p * Real.exp ((n : ℝ) * (te a - te b)))
          (q * Real.exp ((n : ℝ) * (te a - te c))) (r * Real.exp ((n : ℝ) * (te c - te b))) := by
    funext n
    exact aDiag_pow_conj_uparShape hab hac hcb te n p q r
  rw [heq]
  exact hfin

/-! ## The target -/

theorem isHoro_Upar {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    Work.EKLContract.IsHoro (Work.EKLContract.Upar hab hac hcb) := by
  refine ⟨isClosed_Upar hab hac hcb, ?_, ?_⟩
  · intro t u hu
    exact aDiag_conj_mem_Upar hab hac hcb t u hu
  · exact ⟨contractExp a b c, upar_contraction hab hac hcb⟩

end Work.EKLContract.Lemmas
