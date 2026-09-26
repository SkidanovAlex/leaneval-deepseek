import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.SellingDefs
import Submission.Work.SG.Data.SepCheck
import Submission.Work.SG.arithRep_eq_data
import Submission.Work.SG.arithRep_conj_eq

/-!
# Separation glue for `sgRep_intEquiv_iff`

Definitions shared by the lemmas that separate the 230 space-group representatives: the
lattice `A ℤ³`, orders of integer vectors modulo a lattice, the intrinsic translation
`v_A = N_A τ(A)`, coboundaries, the symmorphy order, and the four invariant families
`elem`/`sym`/`pair`/`hand` used by `Submission.Work.SG.Data.SepTab`.

Everything is phrased with integer matrices `IMat = Matrix (Fin 3) (Fin 3) ℤ` and their
real images; `latImg A` is `A ℤ³` viewed as an additive subgroup of `ℝ³`.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open scoped BigOperators
open Classical

/-! ## 1. Integer / real coordinate vectors -/

/-! Integer coordinate vectors.  The local duplicate of `IVec : Type := Fin 3 → ℤ` that used
this name has been removed: `IVec` now comes from `Submission.Work.SG.SellingDefs`, so the
separation branch and the Selling branch can be imported together. -/

/-- The integer vector as a real vector. -/
def toRVec (v : IVec) : Fin 3 → ℝ := fun i => (v i : ℝ)

/-- The integer matrix as a real matrix. -/
def toRMat (A : IMat) : Matrix (Fin 3) (Fin 3) ℝ := A.map (Int.castRingHom ℝ)

@[simp] theorem toRVec_add (v w : IVec) : toRVec (v + w) = toRVec v + toRVec w := by
  funext i; simp [toRVec]

@[simp] theorem toRVec_neg (v : IVec) : toRVec (-v) = -toRVec v := by
  funext i; simp [toRVec]

@[simp] theorem toRVec_zero : toRVec (0 : IVec) = 0 := by
  funext i; simp [toRVec]

@[simp] theorem toRVec_sub (v w : IVec) : toRVec (v - w) = toRVec v - toRVec w := by
  funext i; simp [toRVec]

@[simp] theorem toRVec_smul (k : ℤ) (v : IVec) : toRVec (k • v) = (k : ℝ) • toRVec v := by
  funext i; simp [toRVec]

theorem toRVec_injective : Function.Injective toRVec := by
  intro v w h
  funext i
  exact Int.cast_injective (congrFun h i)

theorem toRMat_mul (A B : IMat) : toRMat (A * B) = toRMat A * toRMat B := by
  rw [toRMat, toRMat, toRMat, Matrix.map_mul]

theorem toRMat_one : toRMat (1 : IMat) = 1 := by
  ext i j
  simp only [toRMat, Matrix.map_apply, Matrix.one_apply]
  split <;> simp

theorem toRMat_pow (A : IMat) (n : ℕ) : toRMat (A ^ n) = toRMat A ^ n := by
  induction n with
  | zero => simp [toRMat_one]
  | succ n ih => rw [pow_succ, pow_succ, toRMat_mul, ih]

theorem toRMat_sum {ι : Type*} (s : Finset ι) (f : ι → IMat) :
    toRMat (∑ i ∈ s, f i) = ∑ i ∈ s, toRMat (f i) := by
  ext a j
  rw [Matrix.sum_apply]
  simp only [toRMat, Matrix.map_apply, Matrix.sum_apply]
  exact map_sum (Int.castRingHom ℝ) (fun c => f c a j) s

theorem mulVec_toRVec (A : IMat) (v : IVec) :
    (toRMat A).mulVec (toRVec v) = toRVec (A.mulVec v) := by
  funext i
  simp [toRMat, toRVec, Matrix.mulVec, dotProduct, Matrix.map_apply]

/-! ## 2. The lattice `A ℤ³` -/

/-- `A ℤ³`, the image of the integer lattice under `A`, as an additive subgroup of `ℝ³`. -/
def latImg (A : IMat) : AddSubgroup (Fin 3 → ℝ) where
  carrier := {v | ∃ w : IVec, (toRMat A).mulVec (toRVec w) = v}
  zero_mem' := ⟨0, by simp [toRMat]⟩
  add_mem' := by
    rintro v₁ v₂ ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
    exact ⟨w₁ + w₂, by rw [toRVec_add, Matrix.mulVec_add, h₁, h₂]⟩
  neg_mem' := by
    rintro v ⟨w, h⟩
    exact ⟨-w, by rw [toRVec_neg, Matrix.mulVec_neg, h]⟩

theorem mem_latImg {A : IMat} {v : Fin 3 → ℝ} :
    v ∈ latImg A ↔ ∃ w : IVec, (toRMat A).mulVec (toRVec w) = v := Iff.rfl

/-- The lattice `ℤ³ ⊂ ℝ³`. -/
def zLat : AddSubgroup (Fin 3 → ℝ) := latImg 1

theorem mem_zLat {v : Fin 3 → ℝ} : v ∈ zLat ↔ ∃ w : IVec, toRVec w = v := by
  rw [zLat, mem_latImg]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, by rw [toRMat_one, Matrix.one_mulVec] at hw; exact hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, by rw [toRMat_one, Matrix.one_mulVec]⟩

theorem toRVec_mem_zLat (w : IVec) : toRVec w ∈ zLat := mem_zLat.mpr ⟨w, rfl⟩

/-! ## 2'. Inverse of a unimodular integer matrix -/

/-- The inverse of a unimodular integer matrix: `(det U) • adjugate U`. -/
def invMat (U : IMat) : IMat := U.det • U.adjugate

theorem mul_invMat {U : IMat} (hU : IsUnit U.det) : U * invMat U = 1 := by
  rw [invMat, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
  rcases Int.isUnit_iff.mp hU with h | h <;> rw [h] <;> norm_num

theorem invMat_mul {U : IMat} (hU : IsUnit U.det) : invMat U * U = 1 := by
  rw [invMat, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
  rcases Int.isUnit_iff.mp hU with h | h <;> rw [h] <;> norm_num

theorem det_invMat {U : IMat} (hU : IsUnit U.det) : (invMat U).det = U.det := by
  rw [invMat, Matrix.det_smul, Matrix.det_adjugate]
  rcases Int.isUnit_iff.mp hU with h | h <;> rw [h] <;> norm_num

theorem isUnit_det_invMat {U : IMat} (hU : IsUnit U.det) : IsUnit (invMat U).det := by
  rw [det_invMat hU]; exact hU

  /-- The additive map `v ↦ A v`. -/
def mulVecHom (A : IMat) : (Fin 3 → ℝ) →+ (Fin 3 → ℝ) where
  toFun v := (toRMat A).mulVec v
  map_zero' := by simp
  map_add' := by intro x y; simp [Matrix.mulVec_add]

@[simp] theorem mulVecHom_apply (A : IMat) (v : Fin 3 → ℝ) :
    mulVecHom A v = (toRMat A).mulVec v := rfl

theorem mulVecHom_one : mulVecHom (1 : IMat) = AddMonoidHom.id (Fin 3 → ℝ) := by
  apply AddMonoidHom.ext
  intro v
  rw [AddMonoidHom.id_apply, mulVecHom_apply, toRMat_one, Matrix.one_mulVec]

theorem mulVecHom_mul (A B : IMat) : mulVecHom (A * B) = (mulVecHom A).comp (mulVecHom B) := by
  apply AddMonoidHom.ext
  intro v
  rw [AddMonoidHom.comp_apply, mulVecHom_apply, mulVecHom_apply, mulVecHom_apply, toRMat_mul,
    Matrix.mulVec_mulVec]

theorem mulVecHom_injective {U : IMat} (hU : IsUnit U.det) : Function.Injective (mulVecHom U) := by
  intro x y h
  have hxy : (toRMat U).mulVec x = (toRMat U).mulVec y := h
  have h2 : (toRMat (invMat U * U)).mulVec x = (toRMat (invMat U * U)).mulVec y := by
    rw [toRMat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
  rwa [invMat_mul hU, toRMat_one, Matrix.one_mulVec, Matrix.one_mulVec] at h2


/-! ## 3. Order of a vector modulo a lattice -/

/-- `o` is the order of `v` in `ℝ³/L`, i.e. `o` is the least positive integer with
`o • v ∈ L`.  (Equivalently `o • v ∈ L` and `(o/p) • v ∉ L` for every prime `p ∣ o`.) -/
theorem latImg_mul (A B : IMat) : latImg (A * B) = (latImg B).map (mulVecHom A) := by
  ext v
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨(toRMat B).mulVec (toRVec w), ⟨w, rfl⟩, ?_⟩
    rw [mulVecHom_apply, ← hw, toRMat_mul, Matrix.mulVec_mulVec]
  · rintro ⟨x, hx, hxu⟩
    obtain ⟨y, hy⟩ := hx
    subst hy
    refine ⟨y, ?_⟩
    rw [← hxu, mulVecHom_apply, toRMat_mul, Matrix.mulVec_mulVec]

theorem mem_latImg_mul {A B : IMat} {v : Fin 3 → ℝ} :
    v ∈ latImg (A * B) ↔ ∃ w ∈ latImg B, (toRMat A).mulVec w = v := by
  rw [latImg_mul, AddSubgroup.mem_map]
  simp only [mulVecHom_apply]

theorem latImg_invMat {U : IMat} (hU : IsUnit U.det) : latImg (invMat U) = zLat := by
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨w, hw⟩ := mem_latImg.mp hv
    rw [mem_zLat]
    refine ⟨(invMat U).mulVec w, ?_⟩
    rw [← hw, mulVec_toRVec]
  · intro v hv
    obtain ⟨w, hw⟩ := mem_zLat.mp hv
    rw [← hw, mem_latImg]
    exact ⟨U.mulVec w, by
      rw [mulVec_toRVec, Matrix.mulVec_mulVec, invMat_mul hU, Matrix.one_mulVec]⟩

theorem latImg_conj_eq_map {U : IMat} (hU : IsUnit U.det) (A : IMat) :
    latImg (U * A * invMat U) = (latImg A).map (mulVecHom U) := by
  have h1 : U * A * invMat U = U * (A * invMat U) := by rw [Matrix.mul_assoc]
  rw [h1, latImg_mul, latImg_mul, latImg_invMat hU, show zLat = latImg (1 : IMat) from rfl,
    ← latImg_mul (A := A) (B := 1), Matrix.mul_one]

theorem latImg_le_conj_iff {U : IMat} (hU : IsUnit U.det) (A B : IMat) :
    latImg (U * A * invMat U) ≤ latImg (U * B * invMat U) ↔ latImg A ≤ latImg B := by
  rw [latImg_conj_eq_map hU, latImg_conj_eq_map hU,
    AddSubgroup.map_le_map_iff_of_injective (mulVecHom_injective hU)]

theorem conj_sub_one {U : IMat} (hU : IsUnit U.det) (A : IMat) :
    U * (A - 1) * invMat U = U * A * invMat U - 1 := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mul_invMat hU]

theorem conj_add_one {U : IMat} (hU : IsUnit U.det) (A : IMat) :
    U * (A + 1) * invMat U = U * A * invMat U + 1 := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, mul_invMat hU]

theorem zLat_map {U : IMat} (hU : IsUnit U.det) : zLat.map (mulVecHom U) = zLat := by
  refine le_antisymm ?_ ?_
  · rintro v ⟨w, hw, rfl⟩
    rw [mem_zLat]
    obtain ⟨y, hy⟩ := mem_zLat.mp hw
    exact ⟨U.mulVec y, by rw [mulVecHom_apply, ← hy, mulVec_toRVec]⟩
  · intro v hv
    rw [mem_zLat] at hv
    obtain ⟨y, hy⟩ := hv
    refine ⟨toRVec ((invMat U).mulVec y), toRVec_mem_zLat _, ?_⟩
    rw [mulVecHom_apply, mulVec_toRVec, Matrix.mulVec_mulVec, mul_invMat hU,
      Matrix.one_mulVec, hy]

theorem mem_zLat_iff_map {U : IMat} (hU : IsUnit U.det) (v : Fin 3 → ℝ) :
    v ∈ zLat ↔ (toRMat U).mulVec v ∈ zLat := by
  constructor
  · intro hv
    have : mulVecHom U v ∈ zLat.map (mulVecHom U) := ⟨v, hv, rfl⟩
    rwa [zLat_map hU] at this
  · intro hv
    have hm : mulVecHom (invMat U) ((toRMat U).mulVec v) ∈ zLat.map (mulVecHom (invMat U)) :=
      ⟨(toRMat U).mulVec v, hv, rfl⟩
    rw [zLat_map (isUnit_det_invMat hU)] at hm
    have hcomp : (toRMat (invMat U)).mulVec ((toRMat U).mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, ← toRMat_mul, invMat_mul hU, toRMat_one, Matrix.one_mulVec]
    rwa [mulVecHom_apply, hcomp] at hm


def IsOrdOf (L : AddSubgroup (Fin 3 → ℝ)) (v : Fin 3 → ℝ) (o : ℕ) : Prop :=
  1 ≤ o ∧ (o : ℤ) • v ∈ L ∧ ∀ p : ℕ, p.Prime → p ∣ o → ¬ ((o / p : ℕ) : ℤ) • v ∈ L

/-- The order of `v` modulo `L` (junk value `0` if `v` has infinite order). -/
noncomputable def ordInLat (L : AddSubgroup (Fin 3 → ℝ)) (v : Fin 3 → ℝ) : ℕ :=
  if h : ∃ o, IsOrdOf L v o then Nat.find h else 0

theorem ordInLat_spec {L : AddSubgroup (Fin 3 → ℝ)} {v : Fin 3 → ℝ}
    (h : ∃ o, IsOrdOf L v o) : IsOrdOf L v (ordInLat L v) := by
  rw [ordInLat, dif_pos h]
  exact Nat.find_spec h

/-! ## 4. Matrix orders, `N_A` and `v_A` -/

/-- The multiplicative order of a matrix, `0` if it is infinite. -/
noncomputable def mOrd (A : IMat) : ℕ :=
  if h : ∃ m : ℕ, 1 ≤ m ∧ A ^ m = 1 then Nat.find h else 0

theorem mOrd_spec {A : IMat} (h : ∃ m, 1 ≤ m ∧ A ^ m = 1) : 1 ≤ mOrd A ∧ A ^ (mOrd A) = 1 := by
  unfold mOrd
  rw [dif_pos h]
  exact Nat.find_spec h

theorem mOrd_min {A : IMat} (h : ∃ m, 1 ≤ m ∧ A ^ m = 1) {m : ℕ}
    (hm : 1 ≤ m) (hm' : A ^ m = 1) : mOrd A ≤ m := by
  unfold mOrd
  rw [dif_pos h]
  exact Nat.find_min' h ⟨hm, hm'⟩

/-- `∑_{i<m} A ^ i`. -/
def Nsum (A : IMat) (m : ℕ) : IMat := ∑ i ∈ Finset.range m, A ^ i

/-- `N_A = ∑_{i < ord(A)} A ^ i`. -/
noncomputable def NZ (A : IMat) : IMat := Nsum A (mOrd A)

/-- The intrinsic translation `v_A = N_A τ(A) ∈ ℝ³`. -/
noncomputable def vA (τ : IMat → Fin 3 → ℝ) (A : IMat) : Fin 3 → ℝ :=
  (toRMat (NZ A)).mulVec (τ A)

/-- The integer vector underlying `v_A` (junk value `0` when `v_A ∉ ℤ³`). -/
noncomputable def vAz (τ : IMat → Fin 3 → ℝ) (A : IMat) : IVec :=
  if h : ∃ v : IVec, toRVec v = vA τ A then h.choose else 0

theorem vAz_spec {τ : IMat → Fin 3 → ℝ} {A : IMat} (h : ∃ v : IVec, toRVec v = vA τ A) :
    toRVec (vAz τ A) = vA τ A := by
  rw [vAz, dif_pos h]; exact h.choose_spec

/-! ## 5. Coboundaries and the symmorphy order -/

/-- `v` is an integral coboundary on `P`: `v A ≡ (1-A) σ (mod ℤ³)` for a real `σ`. -/
def IsCob (P : Set IMat) (v : IMat → Fin 3 → ℝ) : Prop :=
  ∃ σ : Fin 3 → ℝ, ∀ A ∈ P, v A - (σ - (toRMat A).mulVec σ) ∈ zLat

/-- `o` is the order of `[τ] ∈ H¹(P, ℝ³/ℤ³)`: `o τ` is a coboundary and `(o/p) τ` is not,
for every prime `p ∣ o`. -/
def SymOrd (P : Set IMat) (τ : IMat → Fin 3 → ℝ) (o : ℕ) : Prop :=
  1 ≤ o ∧ IsCob P (fun A => (o : ℝ) • τ A) ∧
    ∀ p : ℕ, p.Prime → p ∣ o → ¬ IsCob P (fun A => ((o / p : ℕ) : ℝ) • τ A)

/-- The symmorphy order of `τ` on `P` (junk value `0` if it does not exist). -/
noncomputable def symOrd (P : Set IMat) (τ : IMat → Fin 3 → ℝ) : ℕ :=
  if h : ∃ o, SymOrd P τ o then Nat.find h else 0

theorem symOrd_spec {P : Set IMat} {τ : IMat → Fin 3 → ℝ} (h : ∃ o, SymOrd P τ o) :
    SymOrd P τ (symOrd P τ) := by
  rw [symOrd, dif_pos h]
  exact Nat.find_spec h

/-! ## 6. The four invariant families of `Data.SepTab` -/

/-- The element table of representative `k` as a finset of integer matrices. -/
def Tk (k : Fin 230) : Finset IMat :=
  ((Data.repArith k.val).elems.map Data.M3.toIMat).toFinset

/-- Key of an element `A` for the `elem` family: `(det, trace, order of v_A in ℤ³/N_Aℤ³)`. -/
noncomputable def keyE (k : Fin 230) (A : IMat) : ℤ × ℤ × ℕ :=
  (A.det, A.trace, ordInLat (latImg (NZ A)) (vA (sgTau k) A))

/-- The `elem` invariant: counts of elements of `Tk k` with a given key. -/
noncomputable def EInv (k : Fin 230) (d t : ℤ) (o : ℕ) : ℕ :=
  ((Tk k).filter fun A => keyE k A = (d, t, o)).card

/-- The `sym` invariant: the order of `[τ_k]` in `H¹`. -/
noncomputable def SInv (k : Fin 230) : ℕ := symOrd (arithRep (sgArith k)) (sgTau k)

/-- `(B - 1) v_A ∈ (B - 1) N_A ℤ³` (the `fix` bit of the `pair` family). -/
def fixBit (k : Fin 230) (A B : IMat) : Prop :=
  ((toRMat B - 1).mulVec (vA (sgTau k) A)) ∈ latImg ((B - 1) * NZ A)

/-- `(B + 1) v_A ∈ (B + 1) N_A ℤ³` (the `afix` bit of the `pair` family). -/
def afixBit (k : Fin 230) (A B : IMat) : Prop :=
  ((toRMat B + 1).mulVec (vA (sgTau k) A)) ∈ latImg ((B + 1) * NZ A)

/-- The six bits of a pair `(A,B)` in the order used by `Data.PairCert.bits`. -/
noncomputable def pairBits (k : Fin 230) (A B : IMat) : List Bool :=
  [if fixBit k A B then true else false, if afixBit k A B then true else false,
   if latImg (A - 1) ≤ latImg (B - 1) then true else false,
   if latImg (A + 1) ≤ latImg (B + 1) then true else false,
   if latImg (A - 1) ≤ latImg (B + 1) then true else false,
   if latImg (A + 1) ≤ latImg (B - 1) then true else false]

/-- The `pair` invariant: counts of ordered pairs of `Tk k` with given keys and bits. -/
noncomputable def PInv (k : Fin 230) (kA kB : ℤ × ℤ × ℕ) (bits : List Bool) : ℕ :=
  (((Tk k) ×ˢ (Tk k)).filter fun p => keyE k p.1 = kA ∧ keyE k p.2 = kB ∧
    pairBits k p.1 p.2 = bits).card

/-! ## 7. Bridges between the flat `Data` certificates and matrices -/

namespace Data


theorem M3.toIMat_mul (A B : M3) : (A.mul B).toIMat = A.toIMat * B.toIMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M3.toIMat, M3.mul, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem M3.toIMat_mulV (A : M3) (v : V3) : A.toIMat.mulVec v.toFun = (A.mulV v).toFun := by
  funext i
  fin_cases i <;> simp [M3.toIMat, M3.mulV, V3.toFun, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem M3.toIMat_det (A : M3) : A.toIMat.det = A.det := by
  rw [Matrix.det_fin_three]
  simp [M3.toIMat, M3.det]
  ring

theorem M3.toIMat_trace (A : M3) : A.toIMat.trace = A.trace := by
  simp [M3.toIMat, M3.trace, Matrix.trace, Fin.sum_univ_three]

theorem M3.toIMat_one : (M3.one).toIMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M3.toIMat, M3.one, Matrix.one_apply]

theorem M3.toIMat_injective : Function.Injective M3.toIMat := by
  intro A B h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  have h12 := congrFun (congrFun h 1) 2
  have h20 := congrFun (congrFun h 2) 0
  have h21 := congrFun (congrFun h 2) 1
  have h22 := congrFun (congrFun h 2) 2
  cases A; cases B
  simp_all [M3.toIMat]



theorem V3.toFun_injective : Function.Injective V3.toFun := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  cases a; cases b
  simp_all [V3.toFun]

theorem V3.toFun_add (u v : V3) : (V3.add u v).toFun = u.toFun + v.toFun := by
  funext i; fin_cases i <;> simp [V3.toFun, V3.add]

theorem V3.toFun_sub (u v : V3) : (V3.sub u v).toFun = u.toFun - v.toFun := by
  funext i; fin_cases i <;> simp [V3.toFun, V3.sub]

theorem V3.toFun_smul (v : V3) (k : ℤ) : (V3.smul k v).toFun = k • v.toFun := by
  funext i; fin_cases i <;> simp [V3.toFun, V3.smul]

theorem V3.dot_zero (φ : V3) : V3.dot φ V3.zero = 0 := by simp [V3.dot, V3.zero]

theorem V3.dot_add (φ u v : V3) : V3.dot φ (V3.add u v) = V3.dot φ u + V3.dot φ v := by
  simp [V3.dot, V3.add]; ring

theorem V3.dot_smul (φ : V3) (c : ℤ) (v : V3) : V3.dot φ (V3.smul c v) = c * V3.dot φ v := by
  simp [V3.dot, V3.smul]; ring

theorem dvd_dot_lin {φ : V3} {m : ℤ} :
    ∀ gs : List V3, (∀ g ∈ gs, m ∣ V3.dot φ g) → ∀ cs : List ℤ, m ∣ V3.dot φ (lin gs cs) := by
  intro gs
  induction gs with
  | nil => intro _ cs; simp [lin, V3.dot_zero]
  | cons g gs ih =>
      intro hgs cs
      cases cs with
      | nil => simp [lin, V3.dot_zero]
      | cons c cs =>
          rw [lin, V3.dot_add, V3.dot_smul]
          exact dvd_add (dvd_mul_of_dvd_right (hgs g (by simp)) c)
            (ih (fun g' hg' => hgs g' (by simp [hg'])) cs)

theorem SpanCert.chk_yes {gs : List V3} {v : V3} {cs : List ℤ}
    (h : SpanCert.chk gs v (.yes cs) = true) : lin gs cs = v := by
  simp only [SpanCert.chk, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem SpanCert.chk_no {gs : List V3} {v : V3} {φ : V3} {m : ℕ}
    (h : SpanCert.chk gs v (.no φ m) = true) : ¬ ∃ cs : List ℤ, lin gs cs = v := by
  simp only [SpanCert.chk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne] at h
  obtain ⟨⟨hm2, hg⟩, hv⟩ := h
  rintro ⟨cs, rfl⟩
  have hd : (m : ℤ) ∣ V3.dot φ (lin gs cs) :=
    dvd_dot_lin gs (fun g hg' => Int.dvd_of_emod_eq_zero (hg g hg')) cs
  exact hv (Int.emod_eq_zero_of_dvd hd)

theorem M3.mulVec_getD (N : M3) (cs : List ℤ) :
    N.toIMat.mulVec (fun i => cs.getD i.val 0) = (lin N.cols cs).toFun := by
  match cs with
  | [] => funext i; fin_cases i <;> simp [M3.toIMat, M3.cols, lin, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, V3.toFun, V3.zero]
  | c :: cs =>
    match cs with
    | [] => funext i; fin_cases i <;> simp [M3.toIMat, M3.cols, lin, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, V3.toFun, V3.zero, V3.add, V3.smul] <;> ring
    | c2 :: cs =>
      match cs with
      | [] => funext i; fin_cases i <;> simp [M3.toIMat, M3.cols, lin, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three, V3.toFun, V3.zero, V3.add, V3.smul] <;> ring
      | c3 :: cs =>
        funext i; fin_cases i <;> simp [M3.toIMat, M3.cols, lin, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three, V3.toFun, V3.zero, V3.add, V3.smul] <;> ring

theorem M3.exists_mulVec_of_lin {N : M3} {cs : List ℤ} {v : V3} (h : lin N.cols cs = v) :
    ∃ w : Fin 3 → ℤ, N.toIMat.mulVec w = v.toFun :=
  ⟨fun i => cs.getD i.val 0, by rw [M3.mulVec_getD, h]⟩


end Data

/-- The tabulated values of the representative cocycles: on the `i`-th element of the class,
`sgTau k A_i = repZ[k][i] / n`.  (This is the content of the sibling deliverable
`sgTau_eq_data`; it is taken as a hypothesis here to keep the separation development
independent of that file.) -/
def TauOnTable (k : Fin 230) : Prop :=
  ∀ i : ℕ, i < (Data.repArith k).n →
    sgTau k ((Data.repArith k).elems.getD i Data.M3.one).toIMat =
      fun c => (((Data.repZ.getD k []).getD i Data.V3.zero).toFun c : ℝ) /
        ((Data.repArith k).n : ℝ)

/-- The facts that a separation entry `Data.Sep` certifies, in the form the assembly consumes
(see the four `*_separates` lemmas and `Data.Sep.chk`). -/
def SepOK : Data.Sep → Prop
  | .elem k l d t o => Data.elemCount k d t o ≠ Data.elemCount l d t o
  | .sym k l a b => Data.SymCert.chk k a = true ∧ Data.SymCert.chk l b = true ∧
      a.o ≤ 48 ∧ b.o ≤ 48 ∧ a.o ≠ b.o
  | .hand k l o h jm ta tb =>
      Data.affIdx k = Data.affIdx l ∧
      ta.length = (Data.repArith k).n ∧ tb.length = (Data.repArith l).n ∧
      (∀ i, i < ta.length → Data.HandCert.chk k i (ta.getD i none) = true) ∧
      (∀ i, i < tb.length → Data.HandCert.chk l i (tb.getD i none) = true) ∧
      ta.countP (fun c => Data.handVal c == some (o, h, jm)) ≠
        tb.countP (fun c => Data.handVal c == some (o, h, jm))
  | .pair k l dA tA oA dB tB oB bits la lb =>
      ∃ ca cb : ℕ, Data.pairCount k (dA, tA, oA) (dB, tB, oB) bits la = some ca ∧
        Data.pairCount l (dA, tA, oA) (dB, tB, oB) bits lb = some cb ∧ ca ≠ cb

end Work.SG
