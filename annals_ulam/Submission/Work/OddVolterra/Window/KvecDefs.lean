import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.Geometry.Ulam.ulam_faa_j
import Submission.Work.OddVolterra.Window.Zrad_jet_bounds
import Submission.Work.OddVolterra.Window.Theta_close_aux
import Submission.Work.OddVolterra.Window.krad_data

/-!
# The jet of the odd Abel kernel on the transition window

Off the diagonal `a < σ` and where the Abel radicand `krad h σ t a > 0`, the two kernels of
`Kvec` are the explicit smooth extensions `k1ext`, `k2ext` of `Work.OddVolterra.Kernel.Diag`:

* `k1ext n h σ t a = faaDiBrunoJ (n+1) (n+1/2) a (kjet h σ t a ·) / √(krad h σ t a)`,
* `k2ext n h σ t a = Σ_{i ≤ n} (n choose i) · faaDiBrunoJ i (n-1/2) a (kjet h σ t a ·)
     · (σ-a)^{n-i} · krad^{n-1/2-i} · ∂^{n-i}(lineSlope h · t) a`,

so each of the two components of `Kvec n h a σ z` is the composition of a *fixed* explicit function
of the finite jet

`(a, σ, t, krad h σ t a, kjet h σ t a ·, h' a, …, h^{(n+1)} a)`

with the jet curve `u ↦ (u, σ, t, krad h σ t u, kjet h σ t u ·, h' u, … )`.  This file sets up that
encoding (`KJIx`, `KJet`), the two component functions `KF1`, `KF2`, and the compact box `KJbox`
and open set `KJopen` used by the general jet-curve lemma `JetCurve_box`.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## The jet index type -/

/-- The index type of the finite jet vector on which the two components of the odd Abel kernel
vector are evaluated.  Besides the point `a`, the slope `σ`, the two chord endpoints `t₁ = -z₀`,
`t₂ = z₁`, the two state derivatives `z₂`, `z₃` and the two radicands `krad h σ tᵢ a`, it carries
the jets of `Zrad h (·,σ,tᵢ)` up to order `n+1` and the derivatives `h^{(1)} a, …, h^{(n+1)} a`. -/
inductive KJIx (n : ℕ) where
  | aa : KJIx n
  | sg : KJIx n
  | t1 : KJIx n
  | t2 : KJIx n
  | kd1 : KJIx n
  | kd2 : KJIx n
  | c2 : KJIx n
  | c3 : KJIx n
  | Z1 : Fin (n + 2) → KJIx n
  | Z2 : Fin (n + 2) → KJIx n
  | w : Fin (n + 1) → KJIx n
  deriving DecidableEq, Fintype

/-- The jet curve of the perturbation `h` at the pair `(σ, z)`: the explicit list of quantities
from which the two Abel kernels `K₁(a,σ,t)`, `K₂(a,σ,t)` (`t = -z₀, z₁`) are computed at the point
`a = u`. -/
def KJet (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) : KJIx n → ℝ
  | .aa => u
  | .sg => σ
  | .t1 => -(z 0)
  | .t2 => z 1
  | .kd1 => krad h σ (-(z 0)) u
  | .kd2 => krad h σ (z 1) u
  | .c2 => z 2
  | .c3 => z 3
  | .Z1 k => kjet h σ (-(z 0)) u k.1
  | .Z2 k => kjet h σ (z 1) u k.1
  | .w j => iteratedDeriv (j.1 + 1) h u

@[simp] lemma KJet_aa (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJet n h σ z u .aa = u := rfl
@[simp] lemma KJet_sg (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJet n h σ z u .sg = σ := rfl
@[simp] lemma KJet_t1 (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJet n h σ z u .t1 = -(z 0) := rfl
@[simp] lemma KJet_t2 (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJet n h σ z u .t2 = z 1 := rfl
@[simp] lemma KJet_kd1 (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJet n h σ z u .kd1 = krad h σ (-(z 0)) u := rfl
@[simp] lemma KJet_kd2 (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJet n h σ z u .kd2 = krad h σ (z 1) u := rfl
@[simp] lemma KJet_c2 (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJet n h σ z u .c2 = z 2 := rfl
@[simp] lemma KJet_c3 (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) :
    KJet n h σ z u .c3 = z 3 := rfl
@[simp] lemma KJet_Z1 (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) (k : Fin (n + 2)) :
    KJet n h σ z u (.Z1 k) = kjet h σ (-(z 0)) u k.1 := rfl
@[simp] lemma KJet_Z2 (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) (k : Fin (n + 2)) :
    KJet n h σ z u (.Z2 k) = kjet h σ (z 1) u k.1 := rfl
@[simp] lemma KJet_w (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (u : ℝ) (j : Fin (n + 1)) :
    KJet n h σ z u (.w j) = iteratedDeriv (j.1 + 1) h u := rfl

/-! ## The `ℕ`-indexed extraction of the finite blocks

The Faà-di-Bruno formula `faaDiBrunoJ m α s v` and the second kernel `k2ext` are indexed by natural
numbers, so the jet blocks `Z1`, `Z2`, `w` are extracted as functions `ℕ → ℝ` (with the value `0`
out of range), which avoids any dependent bound in the summands. -/

/-- The `ℕ`-indexed extraction of the first radicand jet block. -/
def KJZ1 (n : ℕ) (v : KJIx n → ℝ) (k : ℕ) : ℝ := if h : k < n + 2 then v (.Z1 ⟨k, h⟩) else 0

/-- The `ℕ`-indexed extraction of the second radicand jet block. -/
def KJZ2 (n : ℕ) (v : KJIx n → ℝ) (k : ℕ) : ℝ := if h : k < n + 2 then v (.Z2 ⟨k, h⟩) else 0

/-- The `ℕ`-indexed extraction of the block of derivatives of `h`. -/
def KJW (n : ℕ) (v : KJIx n → ℝ) (k : ℕ) : ℝ := if h : k < n + 1 then v (.w ⟨k, h⟩) else 0

/-- The radicand jet of `Kernel.Diag` is the jet of `Zrad`, the radicand of the Abel kernels in
the normalisation of `KernelExt`: `(σ - v) krad h σ t v = line h σ t ^ 2 - line h v t ^ 2`. -/
lemma kjet_eq_Zrad {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (σ t a : ℝ) (i : ℕ) :
    kjet h σ t a i = iteratedDeriv i (fun v : ℝ => KernelExt.Zrad h (v, σ, t)) a := by
  unfold kjet KernelExt.Zrad
  congr 1
  funext v
  rw [← psi_eq_mul_krad hh σ t v]
  rfl

lemma KJZ1_of_lt (n : ℕ) (v : KJIx n → ℝ) {k : ℕ} (hk : k < n + 2) :
    KJZ1 n v k = v (.Z1 ⟨k, hk⟩) := dif_pos hk

lemma KJZ2_of_lt (n : ℕ) (v : KJIx n → ℝ) {k : ℕ} (hk : k < n + 2) :
    KJZ2 n v k = v (.Z2 ⟨k, hk⟩) := dif_pos hk

lemma KJW_of_lt (n : ℕ) (v : KJIx n → ℝ) {k : ℕ} (hk : k < n + 1) :
    KJW n v k = v (.w ⟨k, hk⟩) := dif_pos hk

@[simp] lemma KJZ1_eq (n : ℕ) (v : KJIx n → ℝ) (k : Fin (n + 2)) :
    KJZ1 n v k.1 = v (.Z1 k) := by
  rw [KJZ1_of_lt n v k.2]

@[simp] lemma KJZ2_eq (n : ℕ) (v : KJIx n → ℝ) (k : Fin (n + 2)) :
    KJZ2 n v k.1 = v (.Z2 k) := by
  rw [KJZ2_of_lt n v k.2]

@[simp] lemma KJW_eq (n : ℕ) (v : KJIx n → ℝ) (k : Fin (n + 1)) :
    KJW n v k.1 = v (.w k) := by
  rw [KJW_of_lt n v k.2]

/-! ## The two scalar formulas and the two component functions -/

/-- The first Abel kernel in terms of the Faà-di-Bruno polynomial of the radicand jet. -/
def KJk1 (n : ℕ) (a : ℝ) (Z : ℕ → ℝ) (kd : ℝ) : ℝ :=
  Commons.Geometry.Ulam.faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) a
      (fun j : Fin (n + 2) => Z j.1) / Real.sqrt kd

/-- The second Abel kernel in terms of the Faà-di-Bruno polynomials of the radicand jet. -/
def KJk2 (n : ℕ) (a σ t : ℝ) (Z : ℕ → ℝ) (kd : ℝ) (W : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : ℝ) *
    Commons.Geometry.Ulam.faaDiBrunoJ i ((n : ℝ) - 1 / 2) a
      (fun j : Fin (i + 1) => Z j.1) *
    (σ - a) ^ (n - i) * kd ^ (((n : ℝ) - 1 / 2) - (i : ℝ)) *
    (if n - i = 0 then t + W 0 else W (n - i))

/-- **The first component of the kernel vector as a function of the jet.** -/
def KF1 (n : ℕ) (v : KJIx n → ℝ) : ℝ :=
  -(KJk1 n (v .aa) (KJZ1 n v) (v .kd1) * v .c2 +
    KJk1 n (v .aa) (KJZ2 n v) (v .kd2) * v .c3)

/-- **The second component of the kernel vector as a function of the jet.** -/
def KF2 (n : ℕ) (v : KJIx n → ℝ) : ℝ :=
  -(KJk2 n (v .aa) (v .sg) (v .t1) (KJZ1 n v) (v .kd1) (KJW n v) * v .c2 +
    KJk2 n (v .aa) (v .sg) (v .t2) (KJZ2 n v) (v .kd2) (KJW n v) * v .c3)

lemma Z1fun (n : ℕ) (v : KJIx n → ℝ) :
    (fun j : Fin (n + 2) => KJZ1 n v j.1) = fun j : Fin (n + 2) => v (.Z1 j) := by
  funext j; exact KJZ1_eq n v j

lemma Z2fun (n : ℕ) (v : KJIx n → ℝ) :
    (fun j : Fin (n + 2) => KJZ2 n v j.1) = fun j : Fin (n + 2) => v (.Z2 j) := by
  funext j; exact KJZ2_eq n v j

lemma Wfun (n : ℕ) (v : KJIx n → ℝ) :
    (fun j : Fin (n + 1) => KJW n v j.1) = fun j : Fin (n + 1) => v (.w j) := by
  funext j; exact KJW_eq n v j

@[simp] lemma KJZ1_self (n : ℕ) (v : KJIx n → ℝ) (k : ℕ) (hk : k < n + 2) :
    (if h : k < n + 2 then v (.Z1 ⟨k, h⟩) else 0) = v (.Z1 ⟨k, hk⟩) := dif_pos hk

lemma KF1_unfold (n : ℕ) (v : KJIx n → ℝ) :
    KF1 n v = -(Commons.Geometry.Ulam.faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) (v .aa)
        (fun j : Fin (n + 2) => v (.Z1 j)) / Real.sqrt (v .kd1) * v .c2 +
      Commons.Geometry.Ulam.faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) (v .aa)
        (fun j : Fin (n + 2) => v (.Z2 j)) / Real.sqrt (v .kd2) * v .c3) := by
  simp only [KF1, KJk1, Z1fun, Z2fun]

/-! ## The compact box and the open set -/

/-- The lower corner of the compact box in which the jet of the window data takes its values. -/
def KJLo (n : ℕ) (Bz : ℝ) : KJIx n → ℝ
  | .aa => 9 / 20
  | .sg => 7 / 10
  | .t1 => -2
  | .t2 => 1 / 5
  | .kd1 => 1 / 100
  | .kd2 => 1 / 100
  | .c2 => -2
  | .c3 => -2
  | .Z1 _ => -Bz
  | .Z2 _ => -Bz
  | .w _ => -1 / 100

/-- The upper corner of the compact box in which the jet of the window data takes its values. -/
def KJHi (n : ℕ) (Bz : ℝ) : KJIx n → ℝ
  | .aa => 1
  | .sg => 1
  | .t1 => -(1 / 5)
  | .t2 => 2
  | .kd1 => 10
  | .kd2 => 10
  | .c2 => 2
  | .c3 => 2
  | .Z1 _ => Bz
  | .Z2 _ => Bz
  | .w _ => 1 / 100

/-- The compact box of the jet-curve lemma. -/
def KJbox (n : ℕ) (Bz : ℝ) : Set (KJIx n → ℝ) := Set.Icc (KJLo n Bz) (KJHi n Bz)

/-- The open set on which the two component functions are smooth: the two radicands are
non-zero. -/
def KJopen (n : ℕ) : Set (KJIx n → ℝ) := {v | 0 < v .kd1 ∧ 0 < v .kd2}

lemma isCompact_KJbox (n : ℕ) (Bz : ℝ) : IsCompact (KJbox n Bz) := isCompact_Icc
lemma convex_KJbox (n : ℕ) (Bz : ℝ) : Convex ℝ (KJbox n Bz) := convex_Icc _ _
lemma isOpen_KJopen (n : ℕ) : IsOpen (KJopen n) := by
  have h : KJopen n = {v : KJIx n → ℝ | 0 < v .kd1} ∩ {v | 0 < v .kd2} := rfl
  rw [h]
  exact IsOpen.inter (isOpen_lt continuous_const (continuous_apply _))
    (isOpen_lt continuous_const (continuous_apply _))

lemma KJbox_subset_KJopen (n : ℕ) (Bz : ℝ) : KJbox n Bz ⊆ KJopen n := by
  intro v hv
  have h1 : KJLo n Bz .kd1 ≤ v .kd1 := hv.1 .kd1
  have h2 : KJLo n Bz .kd2 ≤ v .kd2 := hv.1 .kd2
  simp only [KJLo] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- The constant `Bz` of the jet bounds: the bound on the radicand jets. -/
def KJbz (n : ℕ) : ℝ := (2 : ℝ) ^ (n + 2) * 100

lemma KJbz_nonneg (n : ℕ) : 0 ≤ KJbz n := by
  simp only [KJbz]; positivity
lemma one_le_KJbz (n : ℕ) : 1 ≤ KJbz n := by
  have h1 : (1 : ℝ) ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
  simp only [KJbz]; linarith
lemma ten_le_KJbz (n : ℕ) : 10 ≤ KJbz n := by
  have h2 : (4 : ℝ) ≤ 2 ^ (n + 2) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  simp only [KJbz]; nlinarith
lemma KJbz_pos (n : ℕ) : 0 < KJbz n := lt_of_lt_of_le (by norm_num) (one_le_KJbz n)

end
end Work.OddVolterra.Window
