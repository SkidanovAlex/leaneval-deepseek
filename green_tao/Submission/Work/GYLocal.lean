import Submission.Work.GYCount
import Submission.Work.GYMajorant
import Submission.Commons.NumberTheory.Sieve.linFormsCond_of_int_coeff
import Submission.Commons.Data.Nat.card_slab_le

/-!
# The localisation step of Green–Tao §9 (`BoxAvgGood → LinFormsCond`)

Green–Tao's proof that the Goldston–Yıldırım majorant `ν` (`GYMaj.nuGT`) satisfies the linear
forms condition (Green–Tao Proposition 9.8) proceeds by chopping `Z_p^t` into `Q^t` almost
equal boxes, applying the box-average asymptotic (their Proposition 9.5, formalised as
`GYMaj.BoxAvg.BoxAvgGood`) on each box, and counting the *non-nice* boxes.

This file formalises that reduction:
* **Clearing denominators** (commons lemma `linFormsCond_of_int_coeff`): it suffices to prove the
  linear forms condition for *integer* coefficients `A i j` with `|A i j| ≤ k! * k`.
* **Boxes**: `Z_p = ⋃_{u < Q} [u p / Q, (u+1) p / Q)`.
* **Nice boxes** give `(1 ± ε_box)^{|I|}` by `BoxAvgGood`; **non-nice boxes** are expanded using
  `ν ≤ 1 + c₀ Λ_R²` and bounded by a constant per box, and the *number* of non-nice boxes is
  `O(Q^{t-1})` (a slab condition on the box index).
-/

open Finset
open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace GYMaj
namespace Local

variable {m t p Q : ℕ}
variable {u : Fin t → Fin Q}
variable {W R : ℕ}
variable {εw : ℝ}

/-! ## The integer boxes -/

/-- Left endpoint of the box with index `u` in coordinate `j`. -/
noncomputable def blo (p Q : ℕ) {t : ℕ} (u : Fin t → Fin Q) (j : Fin t) : ℕ := (u j).val * p / Q

/-- Right endpoint of the box with index `u` in coordinate `j`. -/
noncomputable def bhi (p Q : ℕ) {t : ℕ} (u : Fin t → Fin Q) (j : Fin t) : ℕ :=
  ((u j).val + 1) * p / Q

/-- The integer box with index `u`: the product of the intervals `[u_j p/Q, (u_j+1) p/Q)`. -/
noncomputable def boxInt (p Q : ℕ) {t : ℕ} (u : Fin t → Fin Q) : Finset (Fin t → ℤ) :=
  Fintype.piFinset (fun j => Finset.Ico ((blo p Q u j : ℕ) : ℤ) ((bhi p Q u j : ℕ) : ℤ))

lemma mem_boxInt {p Q : ℕ} {t : ℕ} {u : Fin t → Fin Q} {x : Fin t → ℤ} :
    x ∈ boxInt p Q u ↔
      ∀ j, ((blo p Q u j : ℕ) : ℤ) ≤ x j ∧ x j < ((bhi p Q u j : ℕ) : ℤ) := by
  simp only [boxInt, Fintype.mem_piFinset, Finset.mem_Ico]

lemma blo_nonneg (u : Fin t → Fin Q) (j : Fin t) : (0 : ℤ) ≤ ((blo p Q u j : ℕ) : ℤ) :=
  Int.natCast_nonneg _

lemma blo_le_bhi (hQ : 0 < Q) {u : Fin t → Fin Q} (j : Fin t) :
    blo p Q u j ≤ bhi p Q u j := by
  refine Nat.div_le_div_right ?_
  exact Nat.mul_le_mul_right p (Nat.le_succ _)

lemma bhi_le_p (hQ : 0 < Q) (hQp : Q ≤ p) {u : Fin t → Fin Q} (j : Fin t) :
    bhi p Q u j ≤ p := by
  have h1 : (u j).val + 1 ≤ Q := by have := (u j).isLt; omega
  have h2 : ((u j).val + 1) * p ≤ Q * p := Nat.mul_le_mul_right p h1
  calc bhi p Q u j = ((u j).val + 1) * p / Q := rfl
    _ ≤ Q * p / Q := Nat.div_le_div_right h2
    _ = p := Nat.mul_div_cancel_left p hQ

/-- The side length of the box is at most `p/Q + 1`. -/
lemma bhi_sub_blo_le (hQ : 0 < Q) {u : Fin t → Fin Q} (j : Fin t) :
    bhi p Q u j - blo p Q u j ≤ p / Q + 1 := by
  have h1 : ((u j).val + 1) * p = (u j).val * p + p := by ring
  have h2 : bhi p Q u j ≤ blo p Q u j + (p / Q + 1) := by
    unfold bhi blo
    rw [h1]
    calc ((u j).val * p + p) / Q
        ≤ (u j).val * p / Q + p / Q + 1 := by
          rw [Nat.add_div hQ]
          split_ifs <;> omega
      _ = _ := rfl
  have h3 := blo_le_bhi (p := p) (Q := Q) hQ (u := u) j
  omega

/-- The side length of the box is at least `p/Q`. -/
lemma div_le_bhi_sub_blo (hQ : 0 < Q) {u : Fin t → Fin Q} (j : Fin t) :
    p / Q ≤ bhi p Q u j - blo p Q u j := by
  have h1 : ((u j).val + 1) * p = (u j).val * p + p := by ring
  have h2 : (u j).val * p / Q + p / Q ≤ ((u j).val + 1) * p / Q := by
    rw [h1, Nat.add_div hQ]
    split_ifs <;> omega
  have h3 := blo_le_bhi (p := p) (Q := Q) hQ (u := u) j
  simp only [bhi, blo]
  omega

/-- The box decomposition of `(Fin p)^t` in terms of the integer boxes. -/
theorem sum_boxInt_eq_sum_boxOf {M : Type*} [AddCommMonoid M] (hp : 0 < p) (hQ : 0 < Q)
    (hQp : Q ≤ p) {t : ℕ} (u : Fin t → Fin Q) (F : (Fin t → Fin p) → M) :
    ∑ x ∈ boxInt p Q u, F (fun j => ⟨(x j).toNat % p, Nat.mod_lt _ hp⟩)
      = ∑ v ∈ boxOf hQ hQp u, F v := by
  classical
  refine Finset.sum_bij (fun x hx => fun j => ⟨(x j).toNat, ?_⟩) ?_ ?_ ?_ ?_
  · -- the image lies in `Fin p`
    have hx' := (mem_boxInt.mp hx) j
    have h0 : (0 : ℤ) ≤ x j := le_trans (blo_nonneg u j) hx'.1
    have h1 : x j < (p : ℤ) := by
      have h2 : ((bhi p Q u j : ℕ) : ℤ) ≤ (p : ℤ) := by
        exact_mod_cast bhi_le_p (p := p) (Q := Q) hQ hQp (u := u) j
      linarith [hx'.2]
    exact (Int.toNat_lt h0).mpr h1
  · -- membership of the image in `boxOf`
    intro x hx
    rw [mem_boxOf_iff]
    intro j
    have hx' := (mem_boxInt.mp hx) j
    have h0 : (0 : ℤ) ≤ x j := le_trans (blo_nonneg u j) hx'.1
    have hblo : ((blo p Q u j : ℕ) : ℤ) ≤ x j := hx'.1
    have hbhi : x j < ((bhi p Q u j : ℕ) : ℤ) := hx'.2
    have hle : blo p Q u j ≤ (x j).toNat := (Int.le_toNat h0).mpr hblo
    have hlt : (x j).toNat < bhi p Q u j := by
      by_contra hc
      push Not at hc
      have hc' : ((bhi p Q u j : ℕ) : ℤ) ≤ x j := (Int.le_toNat h0).mp hc
      linarith
    exact ⟨hle, hlt⟩
  · -- injectivity
    intro a₁ ha₁ a₂ ha₂ h
    funext j
    have h1 := congrFun h j
    simp only [Fin.mk.injEq] at h1
    have h0₁ : (0 : ℤ) ≤ a₁ j := le_trans (blo_nonneg u j) (mem_boxInt.mp ha₁ j).1
    have h0₂ : (0 : ℤ) ≤ a₂ j := le_trans (blo_nonneg u j) (mem_boxInt.mp ha₂ j).1
    have h2 : (a₁ j).toNat = (a₂ j).toNat := h1
    have h3 : ((a₁ j).toNat : ℤ) = a₁ j := Int.toNat_of_nonneg h0₁
    have h4 : ((a₂ j).toNat : ℤ) = a₂ j := Int.toNat_of_nonneg h0₂
    omega
  · -- surjectivity
    intro v hv
    refine ⟨fun j => ((v j).val : ℤ), ?_, ?_⟩
    · rw [mem_boxInt]
      intro j
      have hv' := ((GYMaj.mem_boxOf_iff hQ hQp (u := u)).mp hv) j
      exact ⟨by exact_mod_cast hv'.1, by exact_mod_cast hv'.2⟩
    · funext j
      apply Fin.ext
      simp only
      exact Int.toNat_natCast (v j).val
  · -- the summands agree
    intro x hx
    congr 1
    funext j
    apply Fin.ext
    have hx' := (mem_boxInt.mp hx) j
    have h0 : (0 : ℤ) ≤ x j := le_trans (blo_nonneg u j) hx'.1
    have h1 : x j < (p : ℤ) := by
      have h2 : ((bhi p Q u j : ℕ) : ℤ) ≤ (p : ℤ) := by
        exact_mod_cast bhi_le_p (p := p) (Q := Q) hQ hQp (u := u) j
      linarith [hx'.2]
    have h2 : (x j).toNat % p = (x j).toNat := Nat.mod_eq_of_lt (by omega)
    simp only [h2]



/-! ## The integer representative of the linear forms -/

/-- The integer linear form `∑_j A_ij x_j + c_i`. -/
def Lint {m t : ℕ} (A : Fin m → Fin t → ℤ) (c : Fin m → ℤ) (x : Fin t → ℤ) (i : Fin m) : ℤ :=
  (∑ j, A i j * x j) + c i

/-- The residue class of the linear form in `ZMod p`. -/
def psi (p : ℕ) {m t : ℕ} (A : Fin m → Fin t → ℤ) (c : Fin m → ℤ) (x : Fin t → ℤ)
    (i : Fin m) : ZMod p :=
  ((Lint A c x i : ℤ) : ZMod p)

/-- The shifted constant `c_i - k_i p` attached to a stable box with shifts `k_i`. -/
def cshift (p : ℕ) {m : ℕ} (ks : Fin m → ℤ) (c : Fin m → ℤ) (i : Fin m) : ℤ :=
  c i - ks i * p

/-- The box `u` is *stable* for the form `i` with shift `k` when the whole range of `Lint` on the
box lies in the half-open interval `[k p, (k+1) p)`.  In that case the "multiple of `p` to
subtract" is the same for every point of the box (Green–Tao's footnote 22), and
`val (ψ_i x) = Lint x i - k p` throughout. -/
def StableAt (p Q : ℕ) {m t : ℕ} (A : Fin m → Fin t → ℤ) (c : Fin m → ℤ)
    (u : Fin t → Fin Q) (i : Fin m) (k : ℤ) : Prop :=
  ∀ x ∈ boxInt p Q u, k * p ≤ Lint A c x i ∧ Lint A c x i < (k + 1) * p

/-- The window test `ε p ≤ v ≤ 2 ε p` on the real representative. -/
def Clip (ε : ℝ) (p : ℕ) (v : ℝ) : Prop := ε * (p : ℝ) ≤ v ∧ v ≤ 2 * ε * (p : ℝ)

lemma stableAt_mono {p Q : ℕ} {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ} {u : Fin t → Fin Q}
    {i : Fin m} {k : ℤ} (h : StableAt p Q A c u i k) :
    ∀ x ∈ boxInt p Q u, (Lint A c x i - k * p).toNat = Lint A c x i - k * p := by
  intro x hx
  rw [Int.toNat_of_nonneg]
  linarith [(h x hx).1]

/-- On a stable box the value in `[0,p)` of `ψ_i(x)` is the shifted integer form. -/
lemma psi_val_of_stable {p Q : ℕ} [NeZero p] {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ}
    {u : Fin t → Fin Q} {i : Fin m} {k : ℤ} (h : StableAt p Q A c u i k) {x : Fin t → ℤ}
    (hx : x ∈ boxInt p Q u) :
    (psi p A c x i).val = (Lint A c x i - k * p).toNat := by
  have hp : (0:ℤ) < p := by
    have h0 : 0 < p := NeZero.pos p
    exact_mod_cast h0
  have h3 : 0 ≤ Lint A c x i - k * p := by linarith [(h x hx).1]
  have h4 : Lint A c x i - k * p < (p : ℤ) := by
    have : (k + 1) * p = k * p + p := by ring
    linarith [(h x hx).2]
  have hp0 : (((p:ℤ) : ZMod p)) = 0 := by
    rw [show ((p:ℤ):ZMod p) = ((p:ℕ):ZMod p) by simp]
    exact ZMod.natCast_self p
  have h1 : ((k * p : ℤ) : ZMod p) = 0 := by rw [Int.cast_mul, hp0, mul_zero]
  have heq : psi p A c x i = ((Lint A c x i - k * p : ℤ) : ZMod p) := by
    unfold psi
    calc ((Lint A c x i : ℤ) : ZMod p)
        = (((Lint A c x i - k * p) + k * p : ℤ) : ZMod p) := by congr 1; ring
      _ = ((Lint A c x i - k * p : ℤ) : ZMod p) + ((k * p : ℤ) : ZMod p) := by push_cast; ring
      _ = ((Lint A c x i - k * p : ℤ) : ZMod p) := by rw [h1, add_zero]
  have hkp : (k * p) % (p:ℤ) = 0 := by rw [Int.mul_emod, Int.emod_self, mul_zero, Int.zero_emod]
  have hmod : Lint A c x i % (p:ℤ) = (Lint A c x i - k * p) % (p:ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have : Lint A c x i - (Lint A c x i - k * p) = k * p := by ring
    rw [this, hkp]
  have hZ : (((psi p A c x i).val : ℤ)) = ((Lint A c x i - k * p).toNat : ℤ) := by
    rw [heq, ZMod.val_intCast (n := p) (Lint A c x i - k * p),
        Int.emod_eq_of_lt h3 h4, Int.toNat_of_nonneg h3]
  exact_mod_cast hZ

/-- `Int.toNat` of `W * m + 1` for `m ≥ 0`. -/
lemma toNat_mul_add_one {W : ℕ} {m : ℤ} (hm : 0 ≤ m) :
    Int.toNat ((W : ℤ) * m + 1) = W * m.toNat + 1 := by
  have h2 : (0:ℤ) ≤ (W:ℤ) * m + 1 := by
    have : (0:ℤ) ≤ (W:ℤ) * m := mul_nonneg (Int.natCast_nonneg W) hm
    linarith
  have h1 : ((((W : ℤ) * m + 1).toNat : ℤ)) = ((W * m.toNat + 1 : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h2]
    rw [show ((W * m.toNat + 1 : ℕ) : ℤ) = (W:ℤ) * m + 1 from by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Int.toNat_of_nonneg hm]]
  exact_mod_cast h1

/-! ## Range bounds on a box -/

lemma boxInt_abs_sub_le (hQ : 0 < Q) {x y : Fin t → ℤ} (hx : x ∈ boxInt p Q u)
    (hy : y ∈ boxInt p Q u) (j : Fin t) : |x j - y j| ≤ ((bhi p Q u j - blo p Q u j : ℕ) : ℤ) := by
  have h1 := (mem_boxInt.mp hx) j
  have h2 := (mem_boxInt.mp hy) j
  have h3 : ((blo p Q u j : ℕ) : ℤ) ≤ ((bhi p Q u j : ℕ) : ℤ) := by
    exact_mod_cast blo_le_bhi (p := p) (Q := Q) hQ (u := u) j
  rw [abs_le]
  constructor <;> omega

/-- **The range bound**: on a box, two values of the linear form differ by at most
`∑_j |A_ij| * (side length)_j`. -/
lemma abs_Lint_sub_le (hQ : 0 < Q) {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ} {x y : Fin t → ℤ}
    (hx : x ∈ boxInt p Q u) (hy : y ∈ boxInt p Q u) (i : Fin m) :
    |Lint A c x i - Lint A c y i|
      ≤ ∑ j, |A i j| * ((bhi p Q u j - blo p Q u j : ℕ) : ℤ) := by
  have hkey : Lint A c x i - Lint A c y i = ∑ j, A i j * (x j - y j) := by
    have hA : (∑ j, A i j * x j) - (∑ j, A i j * y j)
        = ∑ j, (A i j * x j - A i j * y j) := by rw [Finset.sum_sub_distrib]
    calc Lint A c x i - Lint A c y i
        = (∑ j, A i j * x j) - (∑ j, A i j * y j) := by unfold Lint; ring
      _ = ∑ j, (A i j * x j - A i j * y j) := hA
      _ = ∑ j, A i j * (x j - y j) := by
            apply Finset.sum_congr rfl; intro j _; ring
  rw [hkey]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [abs_mul]
  have h1 : |x j - y j| ≤ ((bhi p Q u j - blo p Q u j : ℕ) : ℤ) := boxInt_abs_sub_le hQ hx hy j
  have h2 : 0 ≤ |A i j| := abs_nonneg _
  calc |A i j| * |x j - y j| ≤ |A i j| * ((bhi p Q u j - blo p Q u j : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = |A i j| * ((bhi p Q u j - blo p Q u j : ℕ) : ℤ) := rfl

/-! ## From an in-window point to a stable box -/

/-- The multiple of `p` to subtract, read off from the representative of `l` in `ZMod p`. -/
lemma exists_shift_of_val {p : ℕ} [NeZero p] (l : ℤ) :
    ∃ k : ℤ, k * p ≤ l ∧ l < (k + 1) * p ∧ (((l : ZMod p).val : ℤ)) = l - k * p := by
  have hp : (0:ℤ) < p := by
    have h0 : 0 < p := NeZero.pos p
    exact_mod_cast h0
  refine ⟨l / p, Int.ediv_mul_le l (by omega), ?_, ?_⟩
  · have := Int.lt_ediv_add_one_mul_self l hp
    linarith
  · rw [ZMod.val_intCast (n := p) l, Int.emod_def]
    ring

/-- **Stability from a single in-window point.**  If the range of `Lint` on the box is at most `Δ`
with `Δ ≤ ε p` and `Δ + 2 ε p < p`, then the existence of one point of the box at which the window
test holds forces the whole box to be stable (Green–Tao's footnote 22). -/
theorem exists_stableAt_of_inWin {p Q : ℕ} [NeZero p] {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ}
    {u : Fin t → Fin Q} {i : Fin m} {ε : ℝ} (Δ : ℤ)
    (hrange : ∀ x ∈ boxInt p Q u, ∀ y ∈ boxInt p Q u, |Lint A c x i - Lint A c y i| ≤ Δ)
    (hΔ0 : (0 : ℝ) ≤ (Δ : ℝ)) (hΔε : (Δ : ℝ) ≤ ε * (p : ℝ))
    (hΔp : (Δ : ℝ) + 2 * ε * (p : ℝ) < (p : ℝ))
    (hin : ∃ x ∈ boxInt p Q u, Clip ε p (((psi p A c x i).val : ℝ))) :
    ∃ k : ℤ, StableAt p Q A c u i k := by
  obtain ⟨x₀, hx₀, hwin⟩ := hin
  obtain ⟨k, hk1, hk2, hk3⟩ := exists_shift_of_val (p := p) (Lint A c x₀ i)
  have hk4 : (0:ℤ) ≤ Lint A c x₀ i - k * p := by linarith
  have hval : (((psi p A c x₀ i).val : ℝ)) = ((Lint A c x₀ i - k * p : ℤ) : ℝ) := by
    exact_mod_cast hk3
  have hlo : ε * (p : ℝ) ≤ ((Lint A c x₀ i - k * p : ℤ) : ℝ) := by rw [← hval]; exact hwin.1
  have hhi : ((Lint A c x₀ i - k * p : ℤ) : ℝ) ≤ 2 * ε * (p : ℝ) := by rw [← hval]; exact hwin.2
  have hsplit₀ : ((Lint A c x₀ i - k * p : ℤ) : ℝ)
      = ((Lint A c x₀ i : ℤ) : ℝ) - (k : ℝ) * (p : ℝ) := by push_cast; ring
  refine ⟨k, fun x hx => ?_⟩
  have h2 := hrange x hx x₀ hx₀
  rw [abs_le] at h2
  have hd : ((Lint A c x i - Lint A c x₀ i : ℤ) : ℝ) = ((Lint A c x i : ℤ) : ℝ)
      - ((Lint A c x₀ i : ℤ) : ℝ) := by push_cast; ring
  have hlo' : -(Δ : ℝ) ≤ ((Lint A c x i : ℤ) : ℝ) - ((Lint A c x₀ i : ℤ) : ℝ) := by
    rw [← hd]; exact_mod_cast h2.1
  have hhi' : ((Lint A c x i : ℤ) : ℝ) - ((Lint A c x₀ i : ℤ) : ℝ) ≤ (Δ : ℝ) := by
    rw [← hd]; exact_mod_cast h2.2
  constructor
  · -- lower bound
    have key : (k : ℝ) * (p : ℝ) ≤ ((Lint A c x i : ℤ) : ℝ) := by
      linarith
    exact_mod_cast key
  · -- upper bound
    have key : ((Lint A c x i : ℤ) : ℝ) < ((k : ℝ) + 1) * (p : ℝ) := by
      linarith
    exact_mod_cast key

/-! ## The value of `ν` on a stable box -/

open Commons.NumberTheory.Sieve (LambdaR)

/-- Green–Tao's constant `c₀ = φ(W)/(W log R)`. -/
noncomputable def c0 (R W : ℕ) : ℝ := (Nat.totient W : ℝ) / ((W : ℝ) * Real.log (R : ℝ))

lemma c0_nonneg {R W : ℕ} (hR : 1 < R) : 0 ≤ c0 R W := by
  unfold c0
  refine div_nonneg (Nat.cast_nonneg _) ?_
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_pos (by exact_mod_cast hR)).le

lemma nuBulk_eq_c0 {R W p : ℕ} (hW : 0 < W) (hR : 1 < R) (z : ZMod p) :
    GYMaj.nuBulk R W p z = c0 R W * (LambdaR R (W * z.val + 1)) ^ 2 := by
  have hW' : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hl : Real.log (R : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hR))
  unfold GYMaj.nuBulk c0
  field_simp

/-- The `W`-tricked linear form of the shifted constant. -/
lemma theta_cshift (W p : ℕ) {m t : ℕ} (A : Fin m → Fin t → ℤ) (ks : Fin m → ℤ)
    (c : Fin m → ℤ) (x : Fin t → ℤ) (i : Fin m) :
    BoxAvg.theta W A (cshift p ks c) x i = (W : ℤ) * (Lint A c x i - ks i * p) + 1 := by
  unfold BoxAvg.theta cshift Lint
  ring

/-- On a stable box, `W * val(ψ_i x) + 1` is exactly `θ_i(x)` for the shifted constant. -/
lemma W_val_eq_theta {p Q : ℕ} [NeZero p] {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ}
    {ks : Fin m → ℤ} {u : Fin t → Fin Q} {i : Fin m} {x : Fin t → ℤ}
    (hstab : StableAt p Q A c u i (ks i)) (hx : x ∈ boxInt p Q u) :
    W * (psi p A c x i).val + 1 = Int.toNat (BoxAvg.theta W A (cshift p ks c) x i) := by
  have hval := psi_val_of_stable hstab hx
  have hnn : 0 ≤ Lint A c x i - ks i * p := by linarith [(hstab x hx).1]
  rw [hval, theta_cshift, ← toNat_mul_add_one (W := W) hnn]

/-- The value of `ν` on a stable box, in the in-window case. -/
theorem nuGT_psi_eq_of_clip {p Q : ℕ} [NeZero p] {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ}
    {ks : Fin m → ℤ} {u : Fin t → Fin Q} {i : Fin m} {x : Fin t → ℤ}
    (hW : 0 < W) (hR : 1 < R)
    (hstab : StableAt p Q A c u i (ks i)) (hx : x ∈ boxInt p Q u)
    (hcl : Clip εw p ((Lint A c x i - ks i * p : ℤ) : ℝ)) :
    GYMaj.nuGT R W p εw (psi p A c x i)
      = c0 R W * (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 := by
  classical
  have hv : ((psi p A c x i).val : ℝ) = ((Lint A c x i - ks i * p : ℤ) : ℝ) := by
    rw [psi_val_of_stable hstab hx]
    exact_mod_cast (Int.toNat_of_nonneg (by linarith [(hstab x hx).1]))
  have hnu : GYMaj.nuGT R W p εw (psi p A c x i) = GYMaj.nuBulk R W p (psi p A c x i) := by
    unfold GYMaj.nuGT
    refine if_pos ?_
    unfold Clip at hcl
    rw [hv]
    exact hcl
  rw [hnu, nuBulk_eq_c0 hW hR, W_val_eq_theta hstab hx]

/-- The value of `ν` on a stable box, in the out-of-window case. -/
theorem nuGT_psi_eq_of_notClip {p Q : ℕ} [NeZero p] {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ}
    {ks : Fin m → ℤ} {u : Fin t → Fin Q} {i : Fin m} {x : Fin t → ℤ}
    (hstab : StableAt p Q A c u i (ks i)) (hx : x ∈ boxInt p Q u)
    (hout : ¬ Clip εw p ((Lint A c x i - ks i * p : ℤ) : ℝ)) :
    GYMaj.nuGT R W p εw (psi p A c x i) = 1 := by
  classical
  have hv : ((psi p A c x i).val : ℝ) = ((Lint A c x i - ks i * p : ℤ) : ℝ) := by
    rw [psi_val_of_stable hstab hx]
    exact_mod_cast (Int.toNat_of_nonneg (by linarith [(hstab x hx).1]))
  unfold GYMaj.nuGT
  refine if_neg ?_
  intro h
  apply hout
  unfold Clip
  rw [hv] at h
  exact h

/-- The out-of-window case, stated directly on the representative: `ν` is exactly `1`. -/
lemma nuGT_psi_eq_one_of_notClip' {p : ℕ} {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ}
    {x : Fin t → ℤ} {i : Fin m} (hout : ¬ Clip εw p (((psi p A c x i).val : ℝ))) :
    GYMaj.nuGT R W p εw (psi p A c x i) = 1 := by
  classical
  unfold GYMaj.nuGT
  refine if_neg ?_
  intro h
  exact hout h

/-- **The upper bound** `ν ≤ 1 + c₀ Λ_R²(θ_i)` on a stable box. -/
theorem nuGT_psi_le {p Q : ℕ} [NeZero p] {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ}
    {ks : Fin m → ℤ} {u : Fin t → Fin Q} {i : Fin m} {x : Fin t → ℤ}
    (hW : 0 < W) (hR : 1 < R)
    (hstab : StableAt p Q A c u i (ks i)) (hx : x ∈ boxInt p Q u) :
    GYMaj.nuGT R W p εw (psi p A c x i)
      ≤ 1 + c0 R W * (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 := by
  classical
  by_cases h : Clip εw p ((Lint A c x i - ks i * p : ℤ) : ℝ)
  · rw [nuGT_psi_eq_of_clip hW hR hstab hx h]
    have h1 : (0:ℝ) ≤ c0 R W * (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 :=
      mul_nonneg (c0_nonneg hR) (sq_nonneg _)
    linarith
  · rw [nuGT_psi_eq_of_notClip hstab hx h]
    have h1 : (0:ℝ) ≤ c0 R W * (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 :=
      mul_nonneg (c0_nonneg hR) (sq_nonneg _)
    linarith

/-! ## The box average of a product over a subset of the forms -/

lemma Ico_eq_Icc_int (a b : ℤ) : Finset.Ico a b = Finset.Icc a (b - 1) := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  omega

/-- Reindexing a product over a `Finset` as a product over `Fin J.card`. -/
lemma prod_subset_eq {m : ℕ} (J : Finset (Fin m)) {M : Type*} [CommMonoid M] (f : Fin m → M) :
    ∏ i ∈ J, f i = ∏ i' : Fin J.card, f (J.equivFin.symm i').1 := by
  rw [← Finset.prod_attach J f]
  have h : (∏ x : ↥J, f ↑x) = ∏ i' : Fin J.card, f (J.equivFin.symm i').1 :=
    Fintype.prod_equiv (J.equivFin) (fun x : ↥J => f ↑x)
      (fun i' => f (J.equivFin.symm i').1) (fun x => by simp)
  rw [Finset.attach_eq_univ]
  exact h

/-- The box as a product of `Icc`'s (the form used by `BoxAvgGood`). -/
lemma boxInt_eq_Icc (p Q : ℕ) {t : ℕ} (u : Fin t → Fin Q) :
    boxInt p Q u = Fintype.piFinset
      (fun j => Finset.Icc (((blo p Q u j : ℕ) : ℤ)) ((((bhi p Q u j : ℕ) : ℤ)) - 1)) := by
  unfold boxInt
  congr 1
  funext j
  exact Ico_eq_Icc_int _ _

/-- The integer side length of the box. -/
noncomputable def sideLen (p Q : ℕ) {t : ℕ} (u : Fin t → Fin Q) (j : Fin t) : ℕ := bhi p Q u j - blo p Q u j

/-- **One box, one subset of the forms**: the box average of `∏_{i ∈ J} Λ_R(θ_i)²` is
`(1 + ε_box)^{|J|}(W log R/φ(W))^{|J|}`, by Green–Tao's box-average asymptotic `BoxAvgGood`
applied to the restricted system. -/
theorem box_product_le {p Q k R W m t : ℕ} {ε_box : ℝ} {A : Fin m → Fin t → ℤ}
    {c ks : Fin m → ℤ} {u : Fin t → Fin Q} {J : Finset (Fin m)}
    (hQ : 0 < Q) (hBox : BoxAvgGood k R W ε_box) (hR1 : 1 ≤ R) (hW : 0 < W) (hε0 : 0 ≤ ε_box)
    (hJ1 : 1 ≤ J.card) (hJm : J.card ≤ k * 2 ^ (k - 1)) (hm : J.card ≤ m)
    (ht1 : 0 < t) (ht2 : t ≤ 3 * k - 4)
    (hne : ∀ i ∈ J, ∃ j, A i j ≠ 0)
    (hprop : ∀ i ∈ J, ∀ i' ∈ J, i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ))
    (hAmax : ∀ i j, (A i j).natAbs ≤ k.factorial * k)
    (hside : ∀ j, (R : ℤ) ^ (10 * m) ≤ ((sideLen p Q u j : ℕ) : ℤ))
    (hpos : ∀ x ∈ boxInt p Q u, ∀ i ∈ J,
        0 < (W : ℤ) * (Lint A c x i - ks i * p) + 1) :
    ∑ x ∈ boxInt p Q u,
        ∏ i ∈ J,
          (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A i j * x j) + cshift p ks c i) + 1))) ^ 2
      ≤ (1 + ε_box) ^ J.card
        * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ J.card
        * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) := by
  classical
  set e := J.equivFin with he
  set A' : Fin J.card → Fin t → ℤ := fun i' j => A (e.symm i').1 j with hA'
  set b' : Fin J.card → ℤ := fun i' => cshift p ks c (e.symm i').1 with hb'
  have hcast : ∀ j, (((bhi p Q u j : ℕ) : ℤ) - ((blo p Q u j : ℕ) : ℤ)) = ((sideLen p Q u j : ℕ) : ℤ) := by
    intro j
    rw [sideLen, Nat.cast_sub (blo_le_bhi (p := p) (Q := Q) hQ (u := u) j)]
  -- the box in `Icc` form
  have hboxI := boxInt_eq_Icc p Q u
  -- the side bound for the restricted cardinality
  have hside' : ∀ j, (R : ℤ) ^ (10 * J.card) ≤ ((sideLen p Q u j : ℕ) : ℤ) := by
    intro j
    refine le_trans ?_ (hside j)
    refine pow_le_pow_right₀ ?_ (by omega)
    exact_mod_cast hR1
  -- hypotheses for `BoxAvgGood`
  have hneA : ∀ i' : Fin J.card, ∃ j, A' i' j ≠ 0 := by
    intro i'
    exact hne (e.symm i').1 (e.symm i').2
  have hpropA : ∀ i' i'' : Fin J.card, i' ≠ i'' → ¬ ∃ lam : ℚ, ∀ j, (A' i'' j : ℚ) = lam * (A' i' j : ℚ) := by
    intro i' i'' hne' h
    have h1 : (e.symm i').1 ≠ (e.symm i'').1 := by
      intro hh
      exact hne' (e.symm.injective (Subtype.ext hh))
    exact hprop (e.symm i').1 (e.symm i').2 (e.symm i'').1 (e.symm i'').2 h1 h
  have hsideA : ∀ j, (R : ℤ) ^ (10 * J.card)
      ≤ (((bhi p Q u j : ℕ) : ℤ)) - (((blo p Q u j : ℕ) : ℤ)) := by
    intro j
    have h1 := hside' j
    have h2 := hcast j
    rw [h2]
    exact h1
  have hposA : ∀ x ∈ Fintype.piFinset
        (fun j => Finset.Icc (((blo p Q u j : ℕ) : ℤ)) ((((bhi p Q u j : ℕ) : ℤ)) - 1)),
      ∀ i' : Fin J.card, 0 < (W : ℤ) * ((∑ j, A' i' j * x j) + b' i') + 1 := by
    intro x hx i'
    rw [← hboxI] at hx
    have h := hpos x hx (e.symm i').1 (e.symm i').2
    have hident : (W : ℤ) * ((∑ j, A' i' j * x j) + b' i') + 1
        = (W : ℤ) * (Lint A c x (e.symm i').1 - ks (e.symm i').1 * p) + 1 := by
      simp only [hA', hb', Lint, cshift]
      ring
    rw [hident]
    exact h
  have happ := hBox J.card t A' b'
    (fun j => (((blo p Q u j : ℕ) : ℤ))) (fun j => (((bhi p Q u j : ℕ) : ℤ)))
    hJ1 hJm ht1 ht2 hneA hpropA (fun i' j => hAmax (e.symm i').1 j) hsideA hposA
  -- rewrite `happ` in terms of `boxInt` and of the original system
  have hsummand : ∀ x : Fin t → ℤ,
      (∏ i : Fin J.card,
          (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A' i j * x j) + b' i) + 1))) ^ 2)
        = ∏ i ∈ J,
          (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A i j * x j) + cshift p ks c i) + 1))) ^ 2 := by
    intro x
    rw [prod_subset_eq J (fun i =>
      (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A i j * x j) + cshift p ks c i) + 1))) ^ 2)]
  -- the side product
  have hSPeq : (∏ j, (((((bhi p Q u j : ℕ) : ℤ)) - (((blo p Q u j : ℕ) : ℤ)) : ℤ) : ℝ))
      = (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) := by
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [hcast j]
    norm_num
  -- the sum
  have hSeq : (∑ x ∈ Fintype.piFinset
        (fun j => Finset.Icc (((blo p Q u j : ℕ) : ℤ)) ((((bhi p Q u j : ℕ) : ℤ)) - 1)),
        ∏ i : Fin J.card,
          (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A' i j * x j) + b' i) + 1))) ^ 2)
      = ∑ x ∈ boxInt p Q u,
          ∏ i ∈ J,
            (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A i j * x j) + cshift p ks c i) + 1))) ^ 2 := by
    rw [hboxI]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact hsummand x
  rw [hSPeq, hSeq] at happ
  have happ' := happ
  -- conclusion
  have hprodpos : 0 < ∏ j, ((sideLen p Q u j : ℕ) : ℝ) := by
    refine Finset.prod_pos (fun j _ => ?_)
    have h1 : (1 : ℤ) ≤ ((sideLen p Q u j : ℕ) : ℤ) := by
      have h3 : (1:ℤ) ≤ (R : ℤ) := by exact_mod_cast hR1
      have h2 : (1 : ℤ) ≤ (R : ℤ) ^ (10 * J.card) := one_le_pow₀ h3
      linarith [hside' j]
    exact_mod_cast h1
  have h2 := (abs_le.mp happ').2
  have h2' := mul_le_mul_of_nonneg_left h2 (le_of_lt hprodpos)
  rw [mul_sub, mul_inv_cancel_left₀ (ne_of_gt hprodpos)] at h2'
  have hXnn : 0 ≤ (W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast hR1))) (Nat.cast_nonneg _)
  have hbase : (1:ℝ) ≤ 1 + ε_box := by linarith
  have hpow : (1 + ε_box) ≤ (1 + ε_box) ^ J.card :=
    le_self_pow₀ hbase (by omega)
  calc ∑ x ∈ boxInt p Q u,
        ∏ i ∈ J,
          (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A i j * x j) + cshift p ks c i) + 1))) ^ 2
      ≤ (∏ j, ((sideLen p Q u j : ℕ) : ℝ))
          * ((1 + ε_box)
              * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ J.card) := by
        linarith [h2']
    _ ≤ (∏ j, ((sideLen p Q u j : ℕ) : ℝ))
          * ((1 + ε_box) ^ J.card
              * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ J.card) := by
        refine mul_le_mul_of_nonneg_left ?_ hprodpos.le
        exact mul_le_mul_of_nonneg_right hpow (pow_nonneg hXnn J.card)
    _ = (1 + ε_box) ^ J.card
          * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ J.card
          * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) := by ring

/-! ## The per-box bound -/

/-- The sum of `∏_i ν(ψ_i(x))` over one box. -/
noncomputable def boxsump (p Q R W : ℕ) (εw : ℝ) {m t : ℕ} (A : Fin m → Fin t → ℤ)
    (c : Fin m → ℤ) (u : Fin t → Fin Q) : ℝ :=
  ∑ x ∈ boxInt p Q u, ∏ i, GYMaj.nuGT R W p εw (psi p A c x i)

/-- No point of the box is in the window. -/
def AllOut (p : ℕ) {m t : ℕ} (A : Fin m → Fin t → ℤ) (c : Fin m → ℤ) (εw : ℝ)
    {Q : ℕ} (u : Fin t → Fin Q) (i : Fin m) : Prop :=
  ∀ x ∈ boxInt p Q u, ¬ Clip εw p (((psi p A c x i).val : ℝ))

/-- Every point of the box is in the window. -/
def AllIn (p : ℕ) {m t : ℕ} (A : Fin m → Fin t → ℤ) (c : Fin m → ℤ) (εw : ℝ)
    {Q : ℕ} (u : Fin t → Fin Q) (i : Fin m) : Prop :=
  ∀ x ∈ boxInt p Q u, Clip εw p (((psi p A c x i).val : ℝ))

lemma card_boxInt (hQ : 0 < Q) {u : Fin t → Fin Q} :
    (boxInt p Q u).card = ∏ j, sideLen p Q u j := by
  unfold boxInt
  rw [Fintype.card_piFinset]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Int.card_Ico]
  rw [sideLen]
  have h1 : (((bhi p Q u j : ℕ) : ℤ) - ((blo p Q u j : ℕ) : ℤ)).toNat
      = bhi p Q u j - blo p Q u j := by
    rw [← Nat.cast_sub (blo_le_bhi (p := p) (Q := Q) hQ (u := u) j)]
    exact Int.toNat_natCast _
  rw [h1]

lemma c0_mul_eq_one {R W : ℕ} (hW : 0 < W) (hR : 1 < R) :
    c0 R W * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) = 1 := by
  have hW' : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hl : Real.log (R : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hR))
  have hφ : (Nat.totient W : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hW).ne'
  unfold c0
  field_simp

/-- Pointwise: `∏_i ν(ψ_i x) ≤ ∏_i (1 + c₀ Λ_R²(θ_i x))`, provided each `i` is either stable or
completely out of the window. -/
theorem prod_nuGT_le {p Q k R W m t : ℕ} [NeZero p] {εw : ℝ} {A : Fin m → Fin t → ℤ} {c ks : Fin m → ℤ}
    {u : Fin t → Fin Q} (hW : 0 < W) (hR : 1 < R)
    (hks : ∀ i, StableAt p Q A c u i (ks i) ∨ AllOut p A c εw u i)
    {x : Fin t → ℤ} (hx : x ∈ boxInt p Q u) :
    ∏ i, GYMaj.nuGT R W p εw (psi p A c x i)
      ≤ ∏ i, (1 + c0 R W *
          (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2) := by
  classical
  have h := Finset.prod_le_prod (s := Finset.univ)
    (f := fun i => GYMaj.nuGT R W p εw (psi p A c x i))
    (g := fun i => 1 + c0 R W *
        (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2)
    (fun i _ => GYMaj.nuGT_nonneg (R := R) (W := W) (ε := εw) hR (psi p A c x i))
    (fun i _ => ?_)
  · simpa using h
  · rcases hks i with hst | hout
    · exact nuGT_psi_le hW hR hst hx
    · rw [nuGT_psi_eq_one_of_notClip' (hout x hx)]
      have h1 : (0:ℝ) ≤ c0 R W *
          (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 :=
        mul_nonneg (c0_nonneg hR) (sq_nonneg _)
      linarith

/-- **The crude per-box bound**: for *any* box the sum of `∏_i ν(ψ_i)` is at most
`(2 + ε_box)^m` times the volume. -/
theorem boxsump_le_shifts {p Q k R W m t : ℕ} [NeZero p] {ε_box εw : ℝ} {A : Fin m → Fin t → ℤ}
    {c ks : Fin m → ℤ} {u : Fin t → Fin Q}
    (hQ : 0 < Q) (hR1 : 1 ≤ R) (hR : 1 < R) (hW : 0 < W) (hε0 : 0 ≤ ε_box)
    (hBox : BoxAvgGood k R W ε_box)
    (hm : m ≤ k * 2 ^ (k - 1)) (ht1 : 0 < t) (ht2 : t ≤ 3 * k - 4)
    (hne : ∀ i, ∃ j, A i j ≠ 0)
    (hprop : ∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ))
    (hAmax : ∀ i j, (A i j).natAbs ≤ k.factorial * k)
    (hside : ∀ j, (R : ℤ) ^ (10 * m) ≤ ((sideLen p Q u j : ℕ) : ℤ))
    (hks : ∀ i, StableAt p Q A c u i (ks i) ∨ AllOut p A c εw u i)
    (hpos : ∀ x ∈ boxInt p Q u, ∀ i, 0 < (W : ℤ) * (Lint A c x i - ks i * p) + 1) :
    boxsump p Q R W εw A c u
      ≤ (2 + ε_box) ^ m * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) := by
  classical
  rw [boxsump]
  have hexp : ∀ x : Fin t → ℤ,
      (∏ i, (1 + c0 R W *
          (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2))
        = ∑ J ∈ (Finset.univ : Finset (Fin m)).powerset,
            ∏ i ∈ J, c0 R W *
              (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 :=
    fun x => Finset.prod_one_add _
  have hstep : ∀ J ∈ (Finset.univ : Finset (Fin m)).powerset,
      (∑ x ∈ boxInt p Q u, ∏ i ∈ J, c0 R W *
          (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2)
        ≤ (1 + ε_box) ^ J.card * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) := by
    intro J hJ
    rw [Finset.mem_powerset] at hJ
    have hcard : J.card ≤ m := by
      have h := Finset.card_le_card hJ
      simpa using h
    have hJm : J.card ≤ k * 2 ^ (k - 1) := le_trans hcard hm
    have hsplit : ∀ x : Fin t → ℤ,
        (∏ i ∈ J, c0 R W *
            (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2)
          = c0 R W ^ J.card * ∏ i ∈ J,
              (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 := by
      intro x
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    by_cases hJ0 : J.card = 0
    · have hJe : J = ∅ := Finset.card_eq_zero.mp hJ0
      subst hJe
      simp only [Finset.card_empty, pow_zero, one_mul, Finset.prod_empty, Finset.sum_const,
        nsmul_eq_mul, mul_one]
      rw [card_boxInt hQ]
      simp
    · have hJ1 : 1 ≤ J.card := by omega
      have hb := box_product_le (p := p) (Q := Q) (k := k) (R := R) (W := W) (m := m) (t := t)
        (ε_box := ε_box) (A := A) (c := c) (ks := ks) (u := u) (J := J)
        hQ hBox hR1 hW hε0 hJ1 hJm hcard ht1 ht2
        (fun i _ => hne i) (fun i _ i' _ h => hprop i i' h) hAmax hside
        (fun x hx i _ => hpos x hx i)
      have hcx : c0 R W ^ J.card
          * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ J.card = 1 := by
        rw [← mul_pow, c0_mul_eq_one hW hR, one_pow]
      calc (∑ x ∈ boxInt p Q u, ∏ i ∈ J, c0 R W *
              (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2)
          = ∑ x ∈ boxInt p Q u, c0 R W ^ J.card * ∏ i ∈ J,
              (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 := by
            refine Finset.sum_congr rfl (fun x _ => hsplit x)
        _ = c0 R W ^ J.card * ∑ x ∈ boxInt p Q u, ∏ i ∈ J,
              (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 := by
            rw [Finset.mul_sum]
        _ ≤ c0 R W ^ J.card * ((1 + ε_box) ^ J.card
              * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ J.card
              * (∏ j, ((sideLen p Q u j : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hb (pow_nonneg (c0_nonneg hR) _)
        _ = (1 + ε_box) ^ J.card * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) := by
            rw [show c0 R W ^ J.card * ((1 + ε_box) ^ J.card
                  * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ J.card
                  * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)))
                = (1 + ε_box) ^ J.card * (c0 R W ^ J.card
                  * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ J.card)
                  * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) by ring]
            rw [hcx, mul_one]
  calc ∑ x ∈ boxInt p Q u, ∏ i, GYMaj.nuGT R W p εw (psi p A c x i)
      ≤ ∑ x ∈ boxInt p Q u, ∏ i, (1 + c0 R W *
          (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2) :=
        Finset.sum_le_sum (fun x hx => prod_nuGT_le (k := k) hW hR hks hx)
    _ = ∑ x ∈ boxInt p Q u, ∑ J ∈ (Finset.univ : Finset (Fin m)).powerset,
          ∏ i ∈ J, c0 R W *
            (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 := by
        refine Finset.sum_congr rfl (fun x _ => hexp x)
    _ = ∑ J ∈ (Finset.univ : Finset (Fin m)).powerset, ∑ x ∈ boxInt p Q u,
          ∏ i ∈ J, c0 R W *
            (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 :=
        Finset.sum_comm
    _ ≤ ∑ J ∈ (Finset.univ : Finset (Fin m)).powerset,
          (1 + ε_box) ^ J.card * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) :=
        Finset.sum_le_sum hstep
    _ = (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) * ∑ J ∈ (Finset.univ : Finset (Fin m)).powerset,
          (1 + ε_box) ^ J.card := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun J _ => ?_)
        ring
    _ = (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) * (1 + (1 + ε_box)) ^ m := by
        congr 1
        have h2 : (∑ J ∈ (Finset.univ : Finset (Fin m)).powerset, (1 + ε_box) ^ J.card)
            = ∑ J ∈ (Finset.univ : Finset (Fin m)).powerset, ∏ i ∈ J, (1 + ε_box) :=
          Finset.sum_congr rfl (fun J _ => (Finset.prod_const (s := J) (1 + ε_box)).symm)
        rw [h2, ← Finset.prod_one_add (s := (Finset.univ : Finset (Fin m)))
          (f := fun _ : Fin m => (1 + ε_box)), Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
    _ = (2 + ε_box) ^ m * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) := by ring


/-- **The sharp per-box bound for a *good* box**: if the indices outside `S` are all completely out
of the window and those inside `S` are all completely in it, then the box sum is at most
`(1 + ε_box)^{|S|}` times the volume. -/
theorem boxsump_le_good {p Q k R W m t : ℕ} [NeZero p] {ε_box εw : ℝ} {A : Fin m → Fin t → ℤ}
    {c ks : Fin m → ℤ} {u : Fin t → Fin Q} (S : Finset (Fin m))
    (hQ : 0 < Q) (hR1 : 1 ≤ R) (hR : 1 < R) (hW : 0 < W) (hε0 : 0 ≤ ε_box)
    (hBox : BoxAvgGood k R W ε_box)
    (hm : m ≤ k * 2 ^ (k - 1)) (ht1 : 0 < t) (ht2 : t ≤ 3 * k - 4)
    (hne : ∀ i ∈ S, ∃ j, A i j ≠ 0)
    (hprop : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ))
    (hAmax : ∀ i j, (A i j).natAbs ≤ k.factorial * k)
    (hside : ∀ j, (R : ℤ) ^ (10 * m) ≤ ((sideLen p Q u j : ℕ) : ℤ))
    (hSout : ∀ i, i ∉ S → AllOut p A c εw u i)
    (hSin : ∀ i ∈ S, ∀ x ∈ boxInt p Q u, Clip εw p (((psi p A c x i).val : ℝ)))
    (hstab : ∀ i ∈ S, StableAt p Q A c u i (ks i))
    (hpos : ∀ x ∈ boxInt p Q u, ∀ i ∈ S,
        0 < (W : ℤ) * (Lint A c x i - ks i * p) + 1) :
    boxsump p Q R W εw A c u
      ≤ (1 + ε_box) ^ S.card * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) := by
  classical
  rw [boxsump]
  have hprod : ∀ x ∈ boxInt p Q u, ∏ i, GYMaj.nuGT R W p εw (psi p A c x i)
      = ∏ i ∈ S, c0 R W *
          (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 := by
    intro x hx
    have h1 : (∏ i : Fin m, GYMaj.nuGT R W p εw (psi p A c x i))
        = ∏ i ∈ S, GYMaj.nuGT R W p εw (psi p A c x i) := by
      rw [Finset.prod_subset (s₁ := S) (s₂ := Finset.univ)
        (f := fun i => GYMaj.nuGT R W p εw (psi p A c x i)) (Finset.subset_univ S)
        (fun i _ hi => nuGT_psi_eq_one_of_notClip' (hSout i hi x hx))]
    rw [h1]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hv : ((psi p A c x i).val : ℝ) = ((Lint A c x i - ks i * p : ℤ) : ℝ) := by
      rw [psi_val_of_stable (hstab i hi) hx]
      exact_mod_cast (Int.toNat_of_nonneg (by linarith [((hstab i hi) x hx).1]))
    exact nuGT_psi_eq_of_clip hW hR (hstab i hi) hx (hv ▸ hSin i hi x hx)
  refine le_trans (Finset.sum_le_sum (fun x hx => le_of_eq (hprod x hx))) ?_
  have hsplit : ∀ x : Fin t → ℤ,
      (∏ i ∈ S, c0 R W *
          (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2)
        = c0 R W ^ S.card * ∏ i ∈ S,
            (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hcard : S.card ≤ m := by
    have h := Finset.card_le_univ S
    simpa using h
  by_cases hS0 : S.card = 0
  · have hSe : S = ∅ := Finset.card_eq_zero.mp hS0
    subst hSe
    simp only [Finset.card_empty, pow_zero, one_mul, Finset.prod_empty, Finset.sum_const,
      nsmul_eq_mul]
    rw [card_boxInt hQ, Nat.cast_prod]
    simp
  · have hS1 : 1 ≤ S.card := by omega
    have hSm : S.card ≤ k * 2 ^ (k - 1) := le_trans hcard hm
    have hb := box_product_le (p := p) (Q := Q) (k := k) (R := R) (W := W) (m := m) (t := t)
      (ε_box := ε_box) (A := A) (c := c) (ks := ks) (u := u) (J := S)
      hQ hBox hR1 hW hε0 hS1 hSm hcard ht1 ht2 hne hprop hAmax hside hpos
    have hcx : c0 R W ^ S.card
        * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ S.card = 1 := by
      rw [← mul_pow, c0_mul_eq_one hW hR, one_pow]
    calc (∑ x ∈ boxInt p Q u, ∏ i ∈ S, c0 R W *
            (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2)
        = ∑ x ∈ boxInt p Q u, c0 R W ^ S.card * ∏ i ∈ S,
            (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 :=
          Finset.sum_congr rfl (fun x _ => hsplit x)
      _ = c0 R W ^ S.card * ∑ x ∈ boxInt p Q u, ∏ i ∈ S,
            (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ c0 R W ^ S.card * ((1 + ε_box) ^ S.card
            * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ S.card
            * (∏ j, ((sideLen p Q u j : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hb (pow_nonneg (c0_nonneg hR) _)
      _ = (1 + ε_box) ^ S.card * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) := by
          rw [show c0 R W ^ S.card * ((1 + ε_box) ^ S.card
                * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ S.card
                * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)))
              = (1 + ε_box) ^ S.card * (c0 R W ^ S.card
                * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ S.card)
                * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) by ring]
          rw [hcx, mul_one]


/-! ## The sum over all boxes -/

/-- The `Fin p → ZMod p` coercion on tuples. -/
def toMod (p : ℕ) {t : ℕ} (v : Fin t → Fin p) : Fin t → ZMod p := fun j => (v j : ZMod p)

/-- The box decomposition of a sum over `(ZMod p)^t`, for real-valued functions. -/
theorem sum_zmod_eq_sum_boxes {t : ℕ} [NeZero p] (hQ : 0 < Q) (hQp : Q ≤ p)
    (G : (Fin t → ZMod p) → ℝ) :
    (∑ z : Fin t → ZMod p, G z)
      = ∑ u : Fin t → Fin Q, ∑ v ∈ boxOf hQ hQp u, G (toMod p v) := by
  refine (Fintype.sum_equiv (finFunEquiv p t) (fun v : Fin t → Fin p => G (toMod p v)) G
    (fun v => by rw [show toMod p v = finFunEquiv p t v from rfl])).symm.trans ?_
  rw [← Finset.sum_biUnion (s := (Finset.univ : Finset (Fin t → Fin Q)))
      (t := boxOf hQ hQp) (f := fun v : Fin t → Fin p => G (toMod p v))
      (fun u _ u' _ h => boxOf_disjoint hQ hQp h), biUnion_boxOf hQ hQp]

/-- **The linear-forms sum as a sum over boxes.** -/
theorem lfc_sum_eq_boxsum {p Q R W m t : ℕ} [NeZero p] (hp : 0 < p) (hQ : 0 < Q) (hQp : Q ≤ p)
    (εw : ℝ) (A : Fin m → Fin t → ℤ) (b : Fin m → ZMod p) :
    (∑ z : Fin t → ZMod p,
        ∏ i, GYMaj.nuGT R W p εw ((∑ j, ((A i j : ℤ) : ZMod p) * z j) + b i))
      = ∑ u : Fin t → Fin Q, boxsump p Q R W εw A (fun i => (b i).val) u := by
  classical
  rw [sum_zmod_eq_sum_boxes (p := p) (Q := Q) hQ hQp
    (fun z => ∏ i, GYMaj.nuGT R W p εw ((∑ j, ((A i j : ℤ) : ZMod p) * z j) + b i))]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← sum_boxInt_eq_sum_boxOf hp hQ hQp u
    (fun v => ∏ i, GYMaj.nuGT R W p εw ((∑ j, ((A i j : ℤ) : ZMod p) * (toMod p v) j) + b i))]
  simp only [toMod]
  rw [boxsump]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have harg : (∑ j, ((A i j : ℤ) : ZMod p) * (((x j).toNat % p : ℕ) : ZMod p)) + b i
      = ((Lint A (fun i => (b i).val) x i : ℤ) : ZMod p) := by
    have hx' := (mem_boxInt.mp hx)
    have hval : ∀ j, (((x j).toNat % p : ℕ) : ZMod p) = ((x j : ℤ) : ZMod p) := by
      intro j
      have h0 : (0 : ℤ) ≤ x j := le_trans (blo_nonneg u j) (hx' j).1
      have h1 : x j < (p : ℤ) := by
        have h2 : ((bhi p Q u j : ℕ) : ℤ) ≤ (p : ℤ) := by
          exact_mod_cast bhi_le_p (p := p) (Q := Q) hQ hQp (u := u) j
        linarith [(hx' j).2]
      have h2 : (x j).toNat % p = (x j).toNat := Nat.mod_eq_of_lt (by omega)
      rw [h2]
      rw [show (x j : ℤ) = (((x j).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h0).symm]
      exact (Int.cast_natCast ((x j).toNat)).symm
    simp only [hval, Lint, Int.cast_sum, Int.cast_mul, Int.cast_add]
    have hthis : ∀ j, ((A i j : ℤ) : ZMod p) * ((x j : ℤ) : ZMod p)
        = ((A i j * x j : ℤ) : ZMod p) := by
      intro j; push_cast; ring
    simp only [hthis]
    rw [← Int.cast_sum]
    congr 1
    simpa using (ZMod.natCast_zmod_val (b i)).symm
  unfold psi
  exact congrArg _ harg

/-- **The boxes tile `(Z_p)^t`**: the sum of the volumes is `p^t`. -/
theorem sum_sideLen (hQ : 0 < Q) (hQp : Q ≤ p) :
    (∑ u : Fin t → Fin Q, (∏ j, ((sideLen p Q u j : ℕ) : ℝ))) = (p : ℝ) ^ t := by
  have hside : ∀ u : Fin t → Fin Q, (∏ j, sideLen p Q u j) = (boxOf hQ hQp u).card := by
    intro u
    rw [card_boxOf hQ hQp u]
    rfl
  have h1 : (∑ u : Fin t → Fin Q, (∏ j, sideLen p Q u j)) = p ^ t := by
    have hcard : (∑ u : Fin t → Fin Q, (boxOf hQ hQp u).card) = p ^ t := by
      rw [← Finset.card_biUnion (s := (Finset.univ : Finset (Fin t → Fin Q)))
        (t := boxOf hQ hQp) (fun u _ u' _ h => boxOf_disjoint hQ hQp h)]
      rw [biUnion_boxOf hQ hQp]
      simp [Fintype.card_fun]
    rw [← hcard]
    exact Finset.sum_congr rfl (fun u _ => hside u)
  calc (∑ u : Fin t → Fin Q, (∏ j, ((sideLen p Q u j : ℕ) : ℝ)))
      = (((∑ u : Fin t → Fin Q, ∏ j, sideLen p Q u j) : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [Nat.cast_prod]
    _ = (p : ℝ) ^ t := by rw [h1]; push_cast; ring

/-! ## The canonical shift of a box -/

open Classical in
/-- The left corner of the box: the point `(⌊u_j p/Q⌋)_j`, which lies in `boxInt p Q u`. -/
noncomputable def corner (p Q : ℕ) {t : ℕ} (u : Fin t → Fin Q) : Fin t → ℤ :=
  fun j => ((blo p Q u j : ℕ) : ℤ)

lemma blo_lt_bhi (hQ : 0 < Q) (hQp : Q ≤ p) (u : Fin t → Fin Q) (j : Fin t) :
    blo p Q u j < bhi p Q u j := by
  have h1 : 1 ≤ p / Q := by
    rw [Nat.le_div_iff_mul_le hQ]
    simpa using hQp
  have h2 : p / Q ≤ bhi p Q u j - blo p Q u j := div_le_bhi_sub_blo (p := p) hQ (u := u) j
  omega

lemma corner_mem (hQ : 0 < Q) (hQp : Q ≤ p) (u : Fin t → Fin Q) :
    corner p Q u ∈ boxInt p Q u := by
  rw [mem_boxInt]
  intro j
  refine ⟨le_rfl, ?_⟩
  show ((blo p Q u j : ℕ) : ℤ) < ((bhi p Q u j : ℕ) : ℤ)
  exact_mod_cast blo_lt_bhi (p := p) (Q := Q) hQ hQp u j

open Classical in
/-- The canonical shift of the box `u` for the form `i`: the stable shift when one exists (read off
from the left corner), and an arbitrary prescribed value `Kout` when the box is completely out of
the window. -/
noncomputable def boxShift (p Q : ℕ) (εw : ℝ) (Kout : ℤ) {m t : ℕ} (A : Fin m → Fin t → ℤ)
    (c : Fin m → ℤ) (u : Fin t → Fin Q) (i : Fin m) : ℤ :=
  if AllOut p A c εw u i then Kout else Lint A c (corner p Q u) i / p

/-- The integer division of `Lint` by `p` read off a stable shift. -/
lemma ediv_eq_of_stable {l : ℤ} {k : ℤ} {p : ℕ} (hp : 0 < p)
    (h1 : k * p ≤ l) (h2 : l < (k + 1) * p) : l / p = k := by
  have hp' : (0:ℤ) < p := by exact_mod_cast hp
  have hle : k ≤ l / p := by
    rw [Int.le_ediv_iff_mul_le (by omega : (0:ℤ) < p)]
    linarith
  have hlt : l / p < k + 1 := by
    rw [Int.ediv_lt_iff_lt_mul hp']
    linarith
  omega

/-- **The canonical shift is stable (or the box is completely out of the window).** -/
theorem boxShift_spec {p Q : ℕ} [NeZero p] {m t : ℕ} (A : Fin m → Fin t → ℤ)
    (c : Fin m → ℤ) (hQ : 0 < Q) (hQp : Q ≤ p) (εw : ℝ) (hεw : 0 < εw)
    (Amax : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ Amax) (Kout : ℤ) (Δ D : ℤ)
    (hD : ∀ (u : Fin t → Fin Q) (j : Fin t), ((sideLen p Q u j : ℕ) : ℤ) ≤ D)
    (hD0 : 0 ≤ D) (hΔ : (t : ℤ) * (Amax : ℤ) * D ≤ Δ)
    (hΔε : (Δ : ℝ) ≤ εw * (p : ℝ)) (hΔp : (Δ : ℝ) + 2 * εw * (p : ℝ) < (p : ℝ))
    (u : Fin t → Fin Q) (i : Fin m) :
    AllOut p A c εw u i ∨ StableAt p Q A c u i (boxShift p Q εw Kout A c u i) := by
  classical
  by_cases hout : AllOut p A c εw u i
  · exact Or.inl hout
  · refine Or.inr ?_
    rw [boxShift, if_neg hout]
    have hp : (0:ℤ) < p := by
      have h0 : 0 < p := NeZero.pos p
      exact_mod_cast h0
    -- the range bound
    have hrange : ∀ x ∈ boxInt p Q u, ∀ y ∈ boxInt p Q u,
        |Lint A c x i - Lint A c y i| ≤ Δ := by
      intro x hx y hy
      refine le_trans (abs_Lint_sub_le (p := p) (Q := Q) hQ hx hy i) ?_
      have h1 : ∀ j : Fin t, |A i j| * ((sideLen p Q u j : ℕ) : ℤ)
          ≤ (Amax : ℤ) * D := by
        intro j
        have h2 : |A i j| ≤ (Amax : ℤ) := by
          have h := hA i j
          have h' : (((A i j).natAbs : ℕ) : ℤ) ≤ (Amax : ℤ) := by exact_mod_cast h
          rwa [Int.natCast_natAbs] at h'
        have h3 : ((sideLen p Q u j : ℕ) : ℤ) ≤ D := hD u j
        have h4 : (0:ℤ) ≤ ((sideLen p Q u j : ℕ) : ℤ) := Int.natCast_nonneg _
        have h5 : (0:ℤ) ≤ |A i j| := abs_nonneg _
        nlinarith [h2, h3, h4, h5, hD0]
      calc ∑ j, |A i j| * ((sideLen p Q u j : ℕ) : ℤ)
          ≤ ∑ _j : Fin t, ((Amax : ℤ) * D) := Finset.sum_le_sum (fun j _ => h1 j)
        _ = (t : ℤ) * ((Amax : ℤ) * D) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = (t : ℤ) * (Amax : ℤ) * D := by ring
        _ ≤ Δ := hΔ
    -- an in-window point
    have hin : ∃ x ∈ boxInt p Q u, Clip εw p (((psi p A c x i).val : ℝ)) := by
      by_contra hc
      push Not at hc
      exact hout hc
    have hΔ0 : (0:ℝ) ≤ (Δ:ℝ) := by
      have h1 : (0:ℤ) ≤ Δ := by
        have h2 : (0:ℤ) ≤ (t : ℤ) * (Amax : ℤ) * D := by positivity
        linarith [hΔ]
      exact_mod_cast h1
    obtain ⟨k, hk⟩ := exists_stableAt_of_inWin (p := p) (Q := Q) (A := A) (c := c) (u := u)
      (i := i) (ε := εw) Δ hrange hΔ0 hΔε hΔp hin
    have hcl := corner_mem (p := p) (Q := Q) hQ hQp u
    have h1 := (hk (corner p Q u) hcl).1
    have h2 := (hk (corner p Q u) hcl).2
    rw [ediv_eq_of_stable (show 0 < p from NeZero.pos p) h1 h2]
    exact hk


/-- **Positivity of the shifted form.**  With the canonical shifts and an out-of-window shift
`Kout ≤ -(t·Amax + 2)`, the form `W (Lint x i - shift·p) + 1` is positive on the box. -/
theorem boxShift_pos {p Q : ℕ} [NeZero p] {m t : ℕ} (A : Fin m → Fin t → ℤ)
    (c : Fin m → ℤ) (hQ : 0 < Q) (hQp : Q ≤ p) (εw : ℝ) (hεw : 0 < εw)
    (Amax : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ Amax) (Kout : ℤ)
    (Δ D : ℤ) (hD : ∀ (u : Fin t → Fin Q) (j : Fin t), ((sideLen p Q u j : ℕ) : ℤ) ≤ D)
    (hD0 : 0 ≤ D) (hΔ : (t : ℤ) * (Amax : ℤ) * D ≤ Δ)
    (hΔε : (Δ : ℝ) ≤ εw * (p : ℝ)) (hΔp : (Δ : ℝ) + 2 * εw * (p : ℝ) < (p : ℝ))
    (hc : ∀ i, (c i).natAbs ≤ (p : ℤ))
    (hKout : Kout ≤ -((t : ℤ) * (Amax : ℤ) + 2))
    (W : ℕ) (u : Fin t → Fin Q) (i : Fin m) (x : Fin t → ℤ) (hx : x ∈ boxInt p Q u) :
    0 < (W : ℤ) * (Lint A c x i - boxShift p Q εw Kout A c u i * p) + 1 := by
  classical
  have hp : (0:ℤ) < p := by
    have h0 : 0 < p := NeZero.pos p
    exact_mod_cast h0
  have hx' := (mem_boxInt.mp hx)
  have hxlt : ∀ j, x j < (p : ℤ) := by
    intro j
    have h2 : ((bhi p Q u j : ℕ) : ℤ) ≤ (p : ℤ) := by
      exact_mod_cast bhi_le_p (p := p) (Q := Q) hQ hQp (u := u) j
    linarith [(hx' j).2]
  have hxnn : ∀ j, (0:ℤ) ≤ x j := fun j => le_trans (blo_nonneg u j) (hx' j).1
  by_cases hout : AllOut p A c εw u i
  · rw [boxShift, if_pos hout]
    -- `Lint x i - Kout * p > 0`
    have h1 : Lint A c x i ≥ -((t : ℤ) * (Amax : ℤ) * (p - 1)) - (p : ℤ) := by
      have hsum : ∑ j, A i j * x j ≥ -((t : ℤ) * (Amax : ℤ) * (p - 1)) := by
        have hb : ∀ j : Fin t, A i j * x j ≥ -((Amax : ℤ) * (p - 1)) := by
          intro j
          have h2 : |A i j| ≤ (Amax : ℤ) := by
            have h := hA i j
            have h' : (((A i j).natAbs : ℕ) : ℤ) ≤ (Amax : ℤ) := by exact_mod_cast h
            rwa [Int.natCast_natAbs] at h'
          have hA' : -(Amax : ℤ) ≤ A i j := by linarith [neg_abs_le (A i j), h2]
          have h3 : x j ≤ (p : ℤ) - 1 := by linarith [hxlt j]
          have h4 : -(Amax : ℤ) * x j ≤ A i j * x j :=
            mul_le_mul_of_nonneg_right hA' (hxnn j)
          have h5 : -(Amax : ℤ) * ((p : ℤ) - 1) ≤ -(Amax : ℤ) * x j :=
            mul_le_mul_of_nonpos_left h3 (by linarith : -(Amax : ℤ) ≤ 0)
          linarith
        calc ∑ j, A i j * x j ≥ ∑ _j : Fin t, (-((Amax : ℤ) * (p - 1))) :=
              Finset.sum_le_sum (fun j _ => hb j)
          _ = -((t : ℤ) * ((Amax : ℤ) * (p - 1))) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
          _ = -((t : ℤ) * (Amax : ℤ) * (p - 1)) := by ring
      have hc' : |c i| ≤ (p : ℤ) := by
        have h := hc i
        have h' : (((c i).natAbs : ℕ) : ℤ) ≤ (p : ℤ) := by exact_mod_cast h
        rwa [Int.natCast_natAbs] at h'
      have := neg_abs_le (c i)
      simp only [Lint]
      linarith
    have h2 : Kout * p ≤ -((t : ℤ) * (Amax : ℤ) + 2) * p := by
      apply mul_le_mul_of_nonneg_right hKout (le_of_lt hp)
    have h3 : (0:ℤ) < Lint A c x i - Kout * p := by
      nlinarith [h1, h2, hp]
    nlinarith [h3, Int.natCast_nonneg W]
  · have hs := boxShift_spec (p := p) (Q := Q) (A := A) (c := c) hQ hQp εw hεw Amax hA Kout Δ D
      hD hD0 hΔ hΔε hΔp u i
    rcases hs with h | h
    · exact absurd h hout
    · have h1 := (h x hx).1
      have hshift : boxShift p Q εw Kout A c u i = Lint A c (corner p Q u) i / p := by
        rw [boxShift, if_neg hout]
      have h3 : (0:ℤ) ≤ Lint A c x i - Lint A c (corner p Q u) i / p * p := by
        rw [← hshift]; linarith [h1]
      rw [hshift]
      nlinarith [h3, Int.natCast_nonneg W]


/-! ## The two-point argument: a mixed box has a point near a window boundary -/

/-- **The two-point argument.**  If a stable box contains an in-window point and an out-of-window
point, then some point of the box has its shifted value within `Δ` (the range of `Lint` on the box)
of one of the two window boundaries `ε p` and `2 ε p`. -/
theorem exists_near_boundary {p Q : ℕ} [NeZero p] {m t : ℕ} {A : Fin m → Fin t → ℤ}
    {c : Fin m → ℤ} {u : Fin t → Fin Q} {i : Fin m} {ks : ℤ} {ε : ℝ}
    (hstab : StableAt p Q A c u i ks)
    (hout : ∃ x ∈ boxInt p Q u, ¬ Clip ε p (((psi p A c x i).val : ℝ)))
    (hin : ∃ x ∈ boxInt p Q u, Clip ε p (((psi p A c x i).val : ℝ)))
    (Δ : ℤ) (hrange : ∀ x ∈ boxInt p Q u, ∀ y ∈ boxInt p Q u,
      |Lint A c x i - Lint A c y i| ≤ Δ) (hΔ0 : (0:ℝ) ≤ (Δ:ℝ)) :
    ∃ x ∈ boxInt p Q u, ∃ α : ℝ, (α = ε * (p : ℝ) ∨ α = 2 * ε * (p : ℝ)) ∧
      |(((Lint A c x i - ks * p : ℤ)) : ℝ) - α| ≤ (Δ : ℝ) := by
  classical
  obtain ⟨x₁, hx₁, hin₁⟩ := hin
  obtain ⟨x₂, hx₂, hout₂⟩ := hout
  have hnn₁ : (0:ℤ) ≤ Lint A c x₁ i - ks * p := by linarith [(hstab x₁ hx₁).1]
  have hnn₂ : (0:ℤ) ≤ Lint A c x₂ i - ks * p := by linarith [(hstab x₂ hx₂).1]
  have hcast₁ : (((psi p A c x₁ i).val : ℝ)) = (((Lint A c x₁ i - ks * p : ℤ)) : ℝ) := by
    rw [psi_val_of_stable hstab hx₁]
    exact_mod_cast (Int.toNat_of_nonneg hnn₁)
  have hcast₂ : (((psi p A c x₂ i).val : ℝ)) = (((Lint A c x₂ i - ks * p : ℤ)) : ℝ) := by
    rw [psi_val_of_stable hstab hx₂]
    exact_mod_cast (Int.toNat_of_nonneg hnn₂)
  rw [hcast₁] at hin₁
  rw [hcast₂] at hout₂
  have hdiff : (((Lint A c x₁ i - ks * p : ℤ)) : ℝ) - (((Lint A c x₂ i - ks * p : ℤ)) : ℝ)
      = (((Lint A c x₁ i - Lint A c x₂ i : ℤ)) : ℝ) := by push_cast; ring
  have hD : |(((Lint A c x₁ i - Lint A c x₂ i : ℤ)) : ℝ)| ≤ (Δ : ℝ) := by
    have h := hrange x₁ hx₁ x₂ hx₂
    exact_mod_cast h
  rcases lt_or_ge ((((Lint A c x₂ i - ks * p : ℤ)) : ℝ)) (ε * (p : ℝ)) with hlt | hge
  · refine ⟨x₂, hx₂, ε * (p : ℝ), Or.inl rfl, ?_⟩
    have h1 : ε * (p : ℝ) - (((Lint A c x₂ i - ks * p : ℤ)) : ℝ) ≤ (Δ : ℝ) := by
      have h2 : ε * (p : ℝ) ≤ (((Lint A c x₁ i - ks * p : ℤ)) : ℝ) := hin₁.1
      have h3 : (((Lint A c x₁ i - ks * p : ℤ)) : ℝ) - (((Lint A c x₂ i - ks * p : ℤ)) : ℝ)
          ≤ (Δ : ℝ) := by
        rw [hdiff]
        exact le_trans (le_abs_self _) hD
      linarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hB : 2 * ε * (p : ℝ) < (((Lint A c x₂ i - ks * p : ℤ)) : ℝ) := by
      by_contra hc
      push Not at hc
      exact hout₂ ⟨hge, hc⟩
    refine ⟨x₂, hx₂, 2 * ε * (p : ℝ), Or.inr rfl, ?_⟩
    have h1 : (((Lint A c x₂ i - ks * p : ℤ)) : ℝ) - 2 * ε * (p : ℝ) ≤ (Δ : ℝ) := by
      have h2 : (((Lint A c x₁ i - ks * p : ℤ)) : ℝ) ≤ 2 * ε * (p : ℝ) := hin₁.2
      have h3 : (((Lint A c x₂ i - ks * p : ℤ)) : ℝ) - (((Lint A c x₁ i - ks * p : ℤ)) : ℝ)
          ≤ (Δ : ℝ) := by
        rw [show (((Lint A c x₂ i - ks * p : ℤ)) : ℝ) - (((Lint A c x₁ i - ks * p : ℤ)) : ℝ)
            = -((((Lint A c x₁ i - ks * p : ℤ)) : ℝ) - (((Lint A c x₂ i - ks * p : ℤ)) : ℝ)) by ring]
        rw [hdiff]
        exact le_trans (neg_le_abs _) hD
      linarith
    rw [abs_of_nonneg (by linarith)]
    linarith


/-- **From a point of the box to the left corner**: the corner is within `Δ` of every point, so the
near-boundary condition transports to the corner with constant `2Δ`. -/
theorem corner_near {p Q : ℕ} [NeZero p] {m t : ℕ} {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ}
    (hQ : 0 < Q) (hQp : Q ≤ p) {u : Fin t → Fin Q} {i : Fin m} {ks : ℤ} {α : ℝ} {Δ : ℤ}
    (hrange : ∀ x ∈ boxInt p Q u, ∀ y ∈ boxInt p Q u, |Lint A c x i - Lint A c y i| ≤ Δ)
    (hΔ0 : (0:ℝ) ≤ (Δ:ℝ)) {x : Fin t → ℤ} (hx : x ∈ boxInt p Q u)
    (h : |(((Lint A c x i - ks * p : ℤ)) : ℝ) - α| ≤ (Δ : ℝ)) :
    |(((Lint A c (corner p Q u) i - ks * p : ℤ)) : ℝ) - α| ≤ 2 * (Δ : ℝ) := by
  have hc := hrange (corner p Q u) (corner_mem (p := p) (Q := Q) hQ hQp u) x hx
  have hc' : |(((Lint A c (corner p Q u) i - Lint A c x i : ℤ)) : ℝ)| ≤ (Δ : ℝ) := by
    exact_mod_cast hc
  have hsplit : (((Lint A c (corner p Q u) i - ks * p : ℤ)) : ℝ) - α
      = (((Lint A c (corner p Q u) i - Lint A c x i : ℤ)) : ℝ)
        + ((((Lint A c x i - ks * p : ℤ)) : ℝ) - α) := by push_cast; ring
  rw [hsplit]
  calc |(((Lint A c (corner p Q u) i - Lint A c x i : ℤ)) : ℝ)
        + ((((Lint A c x i - ks * p : ℤ)) : ℝ) - α)|
      ≤ |(((Lint A c (corner p Q u) i - Lint A c x i : ℤ)) : ℝ)|
        + |(((Lint A c x i - ks * p : ℤ)) : ℝ) - α| := abs_add_le _ _
    _ ≤ (Δ : ℝ) + (Δ : ℝ) := add_le_add hc' h
    _ = 2 * (Δ : ℝ) := by ring


end Local
end GYMaj
