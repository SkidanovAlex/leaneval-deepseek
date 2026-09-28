import Mathlib
import Submission.Work.Projective.CPn

/-!
# The complement of a point in `ℂP^{n+1}` is homotopy equivalent to `ℂPⁿ`

The open set `cpV (n+1) = ⋃_{i ≠ 0} chartSet i ⊆ ℂP^{n+1}` is the complement of the point
`cpOrigin (n+1) = [1 : 0 : … : 0]`.  Dropping the `0`-th coordinate gives a retraction
`[z₀ : z₁ : … : z_{n+1}] ↦ [z₁ : … : z_{n+1}]` onto the hyperplane
`{[0 : z₁ : … : z_{n+1}]} ≅ ℂPⁿ`, and `[t z₀ : z₁ : … : z_{n+1}]` (`t ∈ [0,1]`) is a homotopy
from the composite to the identity.  Hence `cpV (n+1)` and `ℂPⁿ` are homotopy equivalent.

Everything is built from Mathlib's `Projectivization.lift`, the quotient map
`cpMk (n+1) : ℂ^{n+2} ∖ {0} → ℂP^{n+1}` (a quotient map by construction of the topology of
`ℂPⁿ`), and the standard charts of `Submission/Work/Projective/Basic.lean`.  This is the general
`n` version of the argument carried out for `n = 1` in
`Submission/Work/Projective/cp2V_cohomology.lean`.
-/

open scoped LinearAlgebra.Projectivization Manifold ContDiff Topology

namespace Work.Projective

noncomputable section

/-! ## Two auxiliary vector operations

`CPV n = Fin (n+1) → ℂ`, so `CPV (n+1) = Fin (n+2) → ℂ`.  We write `tailFun` for "delete the
`0`-th coordinate" and `consFun` for "insert a `0` as the `0`-th coordinate". -/

/-- The vector obtained from `v ∈ ℂ^{n+2}` by deleting its `0`-th coordinate. -/
def tailFun {n : ℕ} (v : CPV (n + 1)) : CPV n := Fin.tail v

/-- The vector `(0, w) ∈ ℂ^{n+2}` attached to `w ∈ ℂ^{n+1}`. -/
def consFun {n : ℕ} (w : CPV n) : CPV (n + 1) := Fin.cons 0 w

@[simp] theorem tailFun_apply {n : ℕ} (v : CPV (n + 1)) (k : Fin (n + 1)) :
    tailFun v k = v k.succ := rfl

@[simp] theorem consFun_zero {n : ℕ} (w : CPV n) : consFun w 0 = 0 := Fin.cons_zero _ _

@[simp] theorem consFun_succ {n : ℕ} (w : CPV n) (k : Fin (n + 1)) :
    consFun w k.succ = w k := Fin.cons_succ _ _ _

theorem tailFun_consFun {n : ℕ} (w : CPV n) : tailFun (consFun w) = w :=
  Fin.tail_cons (α := fun _ => ℂ) 0 w

theorem tailFun_zero {n : ℕ} : tailFun (0 : CPV (n + 1)) = 0 := funext fun _ => rfl

theorem consFun_eq_zero_iff {n : ℕ} (w : CPV n) : consFun w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have : tailFun (consFun w) = tailFun (0 : CPV (n + 1)) := congrArg tailFun h
    rwa [tailFun_consFun, tailFun_zero] at this
  · rintro rfl
    funext j
    induction j using Fin.cases with
    | zero => simp
    | succ k => simp

theorem consFun_smul {n : ℕ} (t : ℂ) (w : CPV n) : consFun (t • w) = t • consFun w := by
  funext j
  induction j using Fin.cases with
  | zero => simp
  | succ k => simp

theorem continuous_consFun {n : ℕ} :
    Continuous (fun w : {w : CPV n // w ≠ 0} => consFun w.1) := by
  refine continuous_pi fun j => ?_
  induction j using Fin.cases with
  | zero => simp only [consFun_zero]; exact continuous_const
  | succ k => simp only [consFun_succ]; exact (continuous_apply k).comp continuous_subtype_val

/-- `cpMk` does not depend on the proof that its vector is nonzero. -/
theorem cpMk_congr {n : ℕ} {v : CPV n} (h1 h2 : v ≠ 0) :
    cpMk n ⟨v, h1⟩ = cpMk n ⟨v, h2⟩ := by congr 1

/-! ## The hyperplane inclusion `ℂPⁿ → ℂP^{n+1}` -/

/-- The nonzero vector `(0, w) ∈ ℂ^{n+2}` attached to a nonzero vector `w ∈ ℂ^{n+1}`. -/
def hypVec {n : ℕ} (w : {w : CPV n // w ≠ 0}) : {v : CPV (n + 1) // v ≠ 0} :=
  ⟨consFun w.1, fun h => w.2 ((consFun_eq_zero_iff w.1).mp h)⟩

/-- The hyperplane inclusion on the level of vectors: `w ↦ [0 : w]`. -/
def hypAux {n : ℕ} (w : {w : CPV n // w ≠ 0}) : CP (n + 1) := cpMk (n + 1) (hypVec w)

theorem hypAux_wd {n : ℕ} (a b : {w : CPV n // w ≠ 0}) (t : ℂ)
    (h : (a : CPV n) = t • (b : CPV n)) : hypAux a = hypAux b := by
  refine (cpMk_eq_iff (n + 1) (hypVec a) (hypVec b)).mpr ⟨t, ?_⟩
  show t • consFun (b : CPV n) = consFun (a : CPV n)
  rw [h, consFun_smul]

/-- **The hyperplane inclusion** `ℂPⁿ → ℂP^{n+1}`, `[z₀ : … : zₙ] ↦ [0 : z₀ : … : zₙ]`. -/
def hypIncl {n : ℕ} : CP n → CP (n + 1) := Projectivization.lift hypAux hypAux_wd

theorem hypIncl_cpMk {n : ℕ} (w : {w : CPV n // w ≠ 0}) :
    hypIncl (cpMk n w) = cpMk (n + 1) (hypVec w) := by
  rw [hypIncl, cpMk_apply, Projectivization.lift_mk]; congr 1

theorem continuous_hypAux {n : ℕ} : Continuous (hypAux (n := n)) :=
  (continuous_cpMk (n + 1)).comp (Continuous.subtype_mk continuous_consFun _)

theorem continuous_hypIncl {n : ℕ} : Continuous (hypIncl (n := n)) := by
  rw [(isQuotientMap_cpMk n).continuous_iff]
  have h : hypIncl ∘ cpMk n = hypAux := funext hypIncl_cpMk
  rw [h]
  exact continuous_hypAux

/-! ## The tail of a vector and the membership in `cpV` -/

/-- A nonzero vector of `ℂ^{n+2}` represents a point of `cpV (n+1)` exactly when its tail (the
coordinates `1, …, n+1`) does not vanish. -/
theorem tailFun_ne_zero_of_mem_cpV {n : ℕ} (v : {v : CPV (n + 1) // v ≠ 0})
    (hv : cpMk (n + 1) v ∈ cpV (n + 1)) : tailFun v.1 ≠ 0 := by
  obtain ⟨i, hi, hmem⟩ := mem_cpV_iff.mp hv
  rw [mem_chartSet_iff] at hmem
  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
  intro h
  exact hmem (by simpa using congrFun h j)

theorem mem_cpV_tailFun_iff {n : ℕ} (v : {v : CPV (n + 1) // v ≠ 0}) :
    cpMk (n + 1) v ∈ cpV (n + 1) ↔ tailFun v.1 ≠ 0 := by
  refine ⟨tailFun_ne_zero_of_mem_cpV v, fun h => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : Fin (n + 1), v.1 k.succ ≠ 0 := by
    by_contra hc; push Not at hc
    exact h (funext fun k => hc k)
  exact mem_cpV_iff.mpr ⟨k.succ, Fin.succ_ne_zero k,
    (mem_chartSet_iff k.succ v).mpr (by simpa using hk)⟩

theorem hypVec_mem {n : ℕ} (v : {w : CPV n // w ≠ 0}) :
    cpMk (n + 1) (hypVec v) ∈ cpV (n + 1) :=
  (mem_cpV_tailFun_iff (hypVec v)).mpr (by
    change tailFun (consFun v.1) ≠ 0
    rw [tailFun_consFun]; exact v.2)

theorem hypIncl_mem {n : ℕ} (p : CP n) : hypIncl p ∈ cpV (n + 1) := by
  obtain ⟨v, rfl⟩ := cpMk_surjective n p
  rw [hypIncl_cpMk]; exact hypVec_mem v

/-- **The hyperplane inclusion** as a continuous map into `cpV (n+1)`. -/
def hypInclCM (n : ℕ) : C(CP n, ↥(cpV (n + 1))) :=
  ⟨fun p => ⟨hypIncl p, hypIncl_mem p⟩, Continuous.subtype_mk continuous_hypIncl hypIncl_mem⟩

/-! ## The retraction `[z₀ : z₁ : …] ↦ [z₁ : …]` -/

/-- The preimage of `cpV (n+1)` under the quotient map `cpMk (n+1)`, as a subtype. -/
abbrev PreV (n : ℕ) : Type := ↥((cpMk (n + 1)) ⁻¹' cpV (n + 1))

/-- The restriction of the quotient map to the preimage of `cpV (n+1)`: a quotient map. -/
def qW (n : ℕ) : C(PreV n, ↥(cpV (n + 1))) :=
  ⟨(cpV (n + 1)).restrictPreimage (cpMk (n + 1)),
    Continuous.subtype_mk ((continuous_cpMk (n + 1)).comp continuous_subtype_val) _⟩

theorem isQuotientMap_qW (n : ℕ) : Topology.IsQuotientMap (qW n) :=
  (isQuotientMap_cpMk (n + 1)).restrictPreimage_isOpen (isOpen_cpV (n + 1))

theorem qW_surjective (n : ℕ) : Function.Surjective (qW n) :=
  (isQuotientMap_qW n).surjective

/-- **The retraction** `[z₀ : z₁ : … : z_{n+1}] ↦ [z₁ : … : z_{n+1}]`, on representatives. -/
def rhoAux {n : ℕ} (v : PreV n) : CP n :=
  cpMk n ⟨tailFun v.1.1, tailFun_ne_zero_of_mem_cpV v.1 v.2⟩

theorem continuous_tailFun {n : ℕ} : Continuous (fun v : PreV n => tailFun v.1.1) := by
  refine continuous_pi fun k => ?_
  show Continuous (fun v : PreV n => v.1.1 k.succ)
  exact (continuous_apply k.succ).comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_rhoAux {n : ℕ} : Continuous (rhoAux (n := n)) :=
  (continuous_cpMk n).comp (Continuous.subtype_mk continuous_tailFun _)

theorem rhoAux_wd {n : ℕ} (a b : PreV n) (h : qW n a = qW n b) :
    rhoAux a = rhoAux b := by
  have h' : cpMk (n + 1) a.1 = cpMk (n + 1) b.1 := congrArg Subtype.val h
  obtain ⟨s, hs⟩ := (cpMk_eq_iff (n + 1) a.1 b.1).mp h'
  refine (cpMk_eq_iff n _ _).mpr ⟨s, ?_⟩
  show s • tailFun b.1.1 = tailFun a.1.1
  funext k
  have hk : s * b.1.1 k.succ = a.1.1 k.succ := by
    simpa [Pi.smul_apply] using congrFun hs k.succ
  simpa [Pi.smul_apply] using hk

/-- **The retraction** `cpV (n+1) → ℂPⁿ`, `[z₀ : z₁ : … : z_{n+1}] ↦ [z₁ : … : z_{n+1}]`,
descended along the quotient map `cpMk (n+1)`. -/
def rho (n : ℕ) : C(↥(cpV (n + 1)), CP n) :=
  (isQuotientMap_qW n).lift ⟨rhoAux, continuous_rhoAux⟩ rhoAux_wd

theorem rho_apply {n : ℕ} (v : PreV n) : rho n (qW n v) = rhoAux v :=
  congrFun (congrArg (fun (k : C(PreV n, CP n)) => (k : PreV n → CP n))
    ((isQuotientMap_qW n).lift_comp ⟨rhoAux, continuous_rhoAux⟩ rhoAux_wd)) v

theorem rhoAux_hypVec {n : ℕ} (w : {w : CPV n // w ≠ 0})
    (hw : cpMk (n + 1) (hypVec w) ∈ cpV (n + 1)) :
    rhoAux ⟨hypVec w, hw⟩ = cpMk n w := by
  change cpMk n ⟨tailFun (hypVec w).1, tailFun_ne_zero_of_mem_cpV (hypVec w) hw⟩ = cpMk n w
  refine congrArg (cpMk n) ?_
  refine Subtype.ext ?_
  change tailFun (consFun w.1) = w.1
  rw [tailFun_consFun]

/-- The retraction followed by the inclusion of the hyperplane is the identity of `ℂPⁿ`. -/
theorem rho_comp_hypIncl (n : ℕ) :
    (rho n).comp (hypInclCM n) = ContinuousMap.id (CP n) := by
  ext p
  obtain ⟨v, rfl⟩ := cpMk_surjective n p
  change rho n (hypInclCM n (cpMk n v)) = cpMk n v
  have h1 : hypInclCM n (cpMk n v) = qW n ⟨hypVec v, hypVec_mem v⟩ := by
    refine Subtype.ext ?_
    show hypIncl (cpMk n v) = cpMk (n + 1) (hypVec v)
    rw [hypIncl_cpMk]
  rw [h1, rho_apply, rhoAux_hypVec]

/-! ## The homotopy `[t z₀ : z₁ : … : z_{n+1}]` -/

/-- The straight-line homotopy `(t, z) ↦ (t z₀, z₁, …, z_{n+1})` on `ℂ^{n+2}`. -/
def shiftVec {n : ℕ} (t : ℝ) (v : CPV (n + 1)) : CPV (n + 1) :=
  Fin.cons ((t : ℂ) * v 0) (Fin.tail v)

@[simp] theorem shiftVec_zero {n : ℕ} (t : ℝ) (v : CPV (n + 1)) :
    shiftVec t v 0 = (t : ℂ) * v 0 := Fin.cons_zero _ _

@[simp] theorem shiftVec_succ {n : ℕ} (t : ℝ) (v : CPV (n + 1)) (k : Fin (n + 1)) :
    shiftVec t v k.succ = v k.succ := Fin.cons_succ _ _ _

theorem tailFun_shiftVec {n : ℕ} (t : ℝ) (v : CPV (n + 1)) :
    tailFun (shiftVec t v) = tailFun v := by
  show Fin.tail (Fin.cons ((t : ℂ) * v 0) (Fin.tail v)) = Fin.tail v
  rw [Fin.tail_cons]

theorem shiftVec_zero_t {n : ℕ} (v : CPV (n + 1)) : shiftVec 0 v = consFun (tailFun v) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [consFun]
  | succ k => simp [consFun]

theorem shiftVec_one_t {n : ℕ} (v : CPV (n + 1)) : shiftVec 1 v = v := by
  have h : shiftVec (1 : ℝ) v = Fin.cons (v 0) (Fin.tail v) := by
    simp only [shiftVec, Complex.ofReal_one, one_mul]
  rw [h, Fin.cons_self_tail]

theorem shiftVec_smul_coord {n : ℕ} (t : ℝ) (s : ℂ) (v : CPV (n + 1)) :
    shiftVec t (s • v) = s • shiftVec t v := by
  funext j
  induction j using Fin.cases with
  | zero => simp only [shiftVec_zero, Pi.smul_apply]; ring
  | succ k => simp only [shiftVec_succ, Pi.smul_apply]

theorem shiftVec_ne_zero {n : ℕ} (t : ℝ) (v : CPV (n + 1)) (hv : tailFun v ≠ 0) :
    shiftVec t v ≠ 0 := by
  intro h
  apply hv
  rw [← tailFun_shiftVec t v, h]
  exact tailFun_zero

/-- The homotopy `[t z₀ : z₁ : …]` on representatives. -/
def Psi {n : ℕ} (p : unitInterval × PreV n) : CP (n + 1) :=
  cpMk (n + 1) ⟨shiftVec (p.1 : ℝ) p.2.1.1,
    shiftVec_ne_zero _ _ (tailFun_ne_zero_of_mem_cpV p.2.1 p.2.2)⟩

theorem continuous_shiftVec {n : ℕ} :
    Continuous fun p : unitInterval × PreV n => shiftVec (p.1 : ℝ) p.2.1.1 := by
  refine continuous_pi fun j => ?_
  have hv : Continuous fun p : unitInterval × PreV n => p.2.1.1 :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  induction j using Fin.cases with
  | zero =>
    simp only [shiftVec_zero]
    exact (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply 0).comp hv)
  | succ k =>
    simp only [shiftVec_succ]
    exact (continuous_apply k.succ).comp hv

theorem continuous_Psi {n : ℕ} : Continuous (Psi (n := n)) :=
  (continuous_cpMk (n + 1)).comp (Continuous.subtype_mk continuous_shiftVec _)

theorem Psi_wd {n : ℕ} (t : unitInterval) (a b : PreV n) (h : qW n a = qW n b) :
    Psi (t, a) = Psi (t, b) := by
  have h' : cpMk (n + 1) a.1 = cpMk (n + 1) b.1 := congrArg Subtype.val h
  obtain ⟨s, hs⟩ := (cpMk_eq_iff (n + 1) a.1 b.1).mp h'
  refine (cpMk_eq_iff (n + 1) _ _).mpr ⟨s, ?_⟩
  show s • shiftVec (t : ℝ) b.1.1 = shiftVec (t : ℝ) a.1.1
  rw [← shiftVec_smul_coord (t : ℝ) s b.1.1, ← hs]

theorem Psi_mem {n : ℕ} (p : unitInterval × PreV n) : Psi p ∈ cpV (n + 1) := by
  show cpMk (n + 1) ⟨shiftVec (p.1 : ℝ) p.2.1.1, _⟩ ∈ cpV (n + 1)
  refine (mem_cpV_tailFun_iff _).mpr ?_
  rw [tailFun_shiftVec]
  exact tailFun_ne_zero_of_mem_cpV p.2.1 p.2.2

theorem Psi_zero {n : ℕ} (v : PreV n) : Psi ((0 : unitInterval), v) = hypIncl (rhoAux v) := by
  have hL : Psi ((0 : unitInterval), v) =
      cpMk (n + 1) (hypVec ⟨tailFun v.1.1, tailFun_ne_zero_of_mem_cpV v.1 v.2⟩) := by
    show cpMk (n + 1) ⟨shiftVec (0 : ℝ) v.1.1, _⟩ = _
    refine congrArg (cpMk (n + 1)) ?_
    refine Subtype.ext ?_
    show shiftVec (0 : ℝ) v.1.1 = consFun (tailFun v.1.1)
    rw [shiftVec_zero_t]
  have hR : hypIncl (rhoAux v) =
      cpMk (n + 1) (hypVec ⟨tailFun v.1.1, tailFun_ne_zero_of_mem_cpV v.1 v.2⟩) := by
    have hr : rhoAux v = cpMk n ⟨tailFun v.1.1, tailFun_ne_zero_of_mem_cpV v.1 v.2⟩ := rfl
    rw [hr, hypIncl_cpMk]
  rw [hL, hR]

theorem Psi_one {n : ℕ} (v : PreV n) :
    Psi ((1 : unitInterval), v) = (qW n v : CP (n + 1)) := by
  show cpMk (n + 1) ⟨shiftVec (1 : ℝ) v.1.1, _⟩ = cpMk (n + 1) v.1
  refine congrArg (cpMk (n + 1)) ?_
  refine Subtype.ext ?_
  show shiftVec (1 : ℝ) v.1.1 = v.1.1
  rw [shiftVec_one_t]

/-! ## The homotopy, descended to `cpV (n+1)` -/

/-- The homotopy `[t z₀ : z₁ : …]` as a map of `ℂP^{n+1}`, defined along a chosen
representative. -/
def phiRaw {n : ℕ} (p : unitInterval × ↥(cpV (n + 1))) : CP (n + 1) :=
  Psi (p.1, Function.surjInv (qW_surjective n) p.2)

theorem phiRaw_eq {n : ℕ} (t : unitInterval) (v : PreV n) :
    phiRaw (t, qW n v) = Psi (t, v) :=
  Psi_wd t _ _ (Function.surjInv_eq (qW_surjective n) (qW n v))

theorem continuous_phiRaw {n : ℕ} : Continuous (phiRaw (n := n)) := by
  refine (isQuotientMap_qW n).continuous_lift_prod_right (g := phiRaw (n := n)) ?_
  have h : (fun p : unitInterval × PreV n => phiRaw (p.1, qW n p.2)) = Psi (n := n) :=
    funext fun p => phiRaw_eq p.1 p.2
  rw [h]
  exact continuous_Psi

theorem phiRaw_mem {n : ℕ} (p : unitInterval × ↥(cpV (n + 1))) : phiRaw p ∈ cpV (n + 1) := by
  obtain ⟨v, hv⟩ := qW_surjective n p.2
  have h : phiRaw p = Psi (p.1, v) :=
    Psi_wd p.1 _ _ (by rw [Function.surjInv_eq (qW_surjective n) p.2, hv])
  rw [h]
  exact Psi_mem (p.1, v)

/-- The homotopy `[t z₀ : z₁ : …]` on `cpV (n+1)`. -/
def phi {n : ℕ} : C(unitInterval × ↥(cpV (n + 1)), ↥(cpV (n + 1))) :=
  ⟨fun p => ⟨phiRaw p, phiRaw_mem p⟩, Continuous.subtype_mk continuous_phiRaw _⟩

theorem phi_zero {n : ℕ} (p : ↥(cpV (n + 1))) : phi (0, p) = hypInclCM n (rho n p) := by
  obtain ⟨v, hv⟩ := qW_surjective n p
  rw [← hv]
  refine Subtype.ext ?_
  show phiRaw ((0 : unitInterval), qW n v) = (hypInclCM n (rho n (qW n v)) : CP (n + 1))
  rw [phiRaw_eq, rho_apply]
  exact Psi_zero v

theorem phi_one {n : ℕ} (p : ↥(cpV (n + 1))) : phi (1, p) = p := by
  obtain ⟨v, hv⟩ := qW_surjective n p
  rw [← hv]
  refine Subtype.ext ?_
  show phiRaw ((1 : unitInterval), qW n v) = (qW n v : CP (n + 1))
  rw [phiRaw_eq]
  exact Psi_one v

/-- The homotopy from the composite `cpV (n+1) → ℂPⁿ → cpV (n+1)` to the identity. -/
def phiHom {n : ℕ} :
    ((hypInclCM n).comp (rho n)).Homotopy (ContinuousMap.id ↥(cpV (n + 1))) :=
  ContinuousMap.Homotopy.mk phi (fun p => phi_zero p) (fun p => phi_one p)

/-- **The complement of a point in `ℂP^{n+1}` is homotopy equivalent to `ℂPⁿ`.** -/
theorem cpnV_homotopyEquiv (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(Work.Projective.cpV (n + 1)) (Work.Projective.CP n)) := by
  have h1 : ((hypInclCM n).comp (rho n)).Homotopic (ContinuousMap.id ↥(cpV (n + 1))) :=
    ⟨phiHom⟩
  have h2 : ((rho n).comp (hypInclCM n)).Homotopic (ContinuousMap.id (CP n)) := by
    rw [rho_comp_hypIncl n]
  exact ⟨ContinuousMap.HomotopyEquiv.mk (rho n) (hypInclCM n) h1 h2⟩

end

end Work.Projective
