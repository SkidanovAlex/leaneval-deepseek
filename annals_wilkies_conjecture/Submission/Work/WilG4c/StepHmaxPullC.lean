/-
  WilG4c — `StepHmaxPullC`: the near-maximality and the curve-point smoothness of the affine
  `x`-pullback of a member, in the conditional form required by `CurveData`.
-/
import Mathlib
import Submission.Work.WilG4c.StepChoiceOut
import Submission.Work.WilG4c.StepTupleDefs
import Submission.Work.WilG4c.StepEngAux
import Submission.Work.WilG4c.StepEngAux2
import Submission.Work.WilG4c.contDiffAt_affine_pullback_iff
import Submission.Work.WilG4c.iterDir_pullX
import Submission.Work.WilG4c.HmaxAux

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical
open scoped Topology

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

theorem hmax_hcurvesm_pullbackC {n r : ℕ} (hr : 1 ≤ r) (f : (Fin (n + 1) → ℝ) → ℝ)
    (α β : ℝ) (hβ0 : 0 < β) (hα0 : 0 ≤ α) (hαβ : α + β ≤ 1) (B B' : Finset ℝ)
    (hBB' : ∀ x ∈ Work.WilkG4c.I, x ∉ (B' : Set ℝ) → α + β * x ∉ (B : Set ℝ))
    (γs : (L : List (Fin (n + 1))) → ℝ → (Fin n → ℝ))
    (γ : (j : ℕ) → List (Fin n) → ℝ → Fin n → ℝ)
    (hγ : γ = fun j M s => γs (LdirOf j M) (α + β * s))
    (hc : Work.WilkG4c.ChoiceOut f r γs) (hb : Work.WilkG4c.FibreBdd f r B) :
    (∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
        x ∈ Work.WilkG4c.I → x ∉ (B' : Set ℝ) → y ∈ WilkiesDesign.openCube n →
        ContDiffAt ℝ (j + M.length)
          (fun u : Fin (n + 1) → ℝ => f (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)))
          (Work.WilkG4c.pt x y) →
      |Work.WilkG4c.iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ)
          (fun u : Fin (n + 1) → ℝ => f (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)))
          (Work.WilkG4c.pt x y)| ≤
        2 * |Work.WilkG4c.iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ)
          (fun u : Fin (n + 1) → ℝ => f (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)))
          (Work.WilkG4c.curveFun (γ j M) x)|) ∧
    (∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
        x ∈ Work.WilkG4c.I → x ∉ (B' : Set ℝ) → y ∈ WilkiesDesign.openCube n →
        ContDiffAt ℝ (j + M.length)
          (fun u : Fin (n + 1) → ℝ => f (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)))
          (Work.WilkG4c.pt x y) →
        ContDiffAt ℝ (j + M.length)
          (fun u : Fin (n + 1) → ℝ => f (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)))
          (Work.WilkG4c.curveFun (γ j M) x)) := by
  have setup : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
      x ∈ Work.WilkG4c.I → x ∉ (B' : Set ℝ) → y ∈ WilkiesDesign.openCube n →
      ContDiffAt ℝ (j + M.length)
        (fun u : Fin (n + 1) → ℝ => f (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)))
        (Work.WilkG4c.pt x y) →
      (α + β * x ∈ Work.WilkG4c.I) ∧ (α + β * x ∉ (B : Set ℝ)) ∧
      ContDiffAt ℝ ((LdirOf j M).length) f (Work.WilkG4c.pt (α + β * x) y) ∧
      ContDiffAt ℝ ((LdirOf j M).length) f
        (Work.WilkG4c.pt (α + β * x) (γs (LdirOf j M) (α + β * x))) ∧
      ContDiffAt ℝ (j + M.length) f (Work.WilkG4c.pt (α + β * x) y) ∧
      ContDiffAt ℝ (j + M.length) f
        (Work.WilkG4c.pt (α + β * x) (γs (LdirOf j M) (α + β * x))) := by
    intro j M x y hjm hx hxB' hy hG
    have hlen : (LdirOf j M).length = j + M.length := LdirOf_length j M
    have hβne : β ≠ 0 := ne_of_gt hβ0
    have hx1 : 0 < x := hx.1
    have hx2 : x < 1 := hx.2
    have hx' : α + β * x ∈ Work.WilkG4c.I := by
      refine ⟨by nlinarith [mul_pos hβ0 hx1, hα0], ?_⟩
      have hlt : β * x < β := by nlinarith [mul_lt_mul_of_pos_left hx2 hβ0]
      linarith
    have hxB : α + β * x ∉ (B : Set ℝ) := hBB' x hx hxB'
    have hcast : (((LdirOf j M).length : ℕ) : WithTop ℕ∞)
        = ((j : WithTop ℕ∞) + (M.length : WithTop ℕ∞)) := by
      rw [hlen, Nat.cast_add]
    have hG' : ContDiffAt ℝ ((LdirOf j M).length)
        (fun u : Fin (n + 1) → ℝ => f (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)))
        (Work.WilkG4c.pt x y) := hcast ▸ hG
    have hGf : ContDiffAt ℝ ((LdirOf j M).length) f (Work.WilkG4c.pt (α + β * x) y) := by
      have h := (Work.WilkG4c.contDiffAt_affine_pullback_iff f α β hβne
        (Work.WilkG4c.pt x y)).mp hG'
      simpa only [Work.WilkG4c.pt_zero, Work.WilkG4c.tail_pt] using h
    have hGf' : ContDiffAt ℝ (j + M.length) f (Work.WilkG4c.pt (α + β * x) y) :=
      hcast.symm ▸ hGf
    have hbdd := hb (LdirOf j M) (by rw [hlen]; omega) (α + β * x) hx' hxB
    have hne : ({y' : Fin n → ℝ | y' ∈ WilkiesDesign.openCube n ∧
        ContDiffAt ℝ ((LdirOf j M).length) f (Work.WilkG4c.pt (α + β * x) y')}).Nonempty :=
      ⟨y, hy, hGf⟩
    obtain ⟨y₀, hy₀, hy₀max⟩ := hmax_nearmax_of_bdd hne
      (fun y' => iteratedFDeriv ℝ ((LdirOf j M).length) f (Work.WilkG4c.pt (α + β * x) y')
        (fun k => Pi.single ((LdirOf j M).get k) 1)) (by simpa using hbdd)
    have hcc := hc (LdirOf j M) (by rw [hlen]; omega) (α + β * x)
      ⟨y₀, hy₀.1, hy₀.2, fun y' hy' hcd' => hy₀max y' ⟨hy', hcd'⟩⟩
    have hGc : ContDiffAt ℝ ((LdirOf j M).length) f
        (Work.WilkG4c.pt (α + β * x) (γs (LdirOf j M) (α + β * x))) := hcc.2.1
    have hGc' : ContDiffAt ℝ (j + M.length) f
        (Work.WilkG4c.pt (α + β * x) (γs (LdirOf j M) (α + β * x))) := hcast.symm ▸ hGc
    exact ⟨hx', hxB, hGf, hGc, hGf', hGc'⟩
  have hcurve : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ),
      Work.WilkG4c.curveFun (γ j M) x
        = Work.WilkG4c.pt x (γs (LdirOf j M) (α + β * x)) := by
    intro j M x
    simp only [Work.WilkG4c.curveFun, hγ]
  constructor
  · intro j M x y hjm hx hxB' hy hG
    obtain ⟨hx', hxB, hGf, hGfc, hGf', hGfc'⟩ := setup j M x y hjm hx hxB' hy hG
    set L : List (Fin (n + 1)) := List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ with hL
    have hlen : L.length = j + M.length := by
      rw [hL, List.length_append, List.length_replicate, List.length_map]
    have hmaxf := Work.WilkG4c.hmax_of_choice_lists (n := n) (p := 0) (r := r)
      (fun _ : Fin 0 → ℝ => f) (fun _ => 0) B γs hc hb
    have hkey : |Work.WilkG4c.iterDir L f (Work.WilkG4c.pt (α + β * x) y)| ≤
        2 * |Work.WilkG4c.iterDir L f
              (Work.WilkG4c.pt (α + β * x) (γs (LdirOf j M) (α + β * x)))| := by
      have h := hmaxf j M (α + β * x) y (by omega) hx' hxB hy hGf'
      simpa only [hL, LdirOf, cvList, canonList, Work.WilkG4c.curveFun] using h
    have hLp : Work.WilkG4c.iterDir L
          (fun u : Fin (n + 1) → ℝ => f (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)))
          (Work.WilkG4c.pt x y)
        = β ^ j * Work.WilkG4c.iterDir L f (Work.WilkG4c.pt (α + β * x) y) := by
      rw [Work.WilG4c.iterDir_pullX f α β x y L (by rw [hlen]; exact hGf'), hL,
        xcount_replicate_map M]
    have hRp : Work.WilkG4c.iterDir L
          (fun u : Fin (n + 1) → ℝ => f (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)))
          (Work.WilkG4c.curveFun (γ j M) x)
        = β ^ j * Work.WilkG4c.iterDir L f
            (Work.WilkG4c.pt (α + β * x) (γs (LdirOf j M) (α + β * x))) := by
      rw [hcurve j M x]
      rw [Work.WilG4c.iterDir_pullX f α β x (γs (LdirOf j M) (α + β * x)) L
        (by rw [hlen]; exact hGfc'), hL, xcount_replicate_map M]
    calc |Work.WilkG4c.iterDir L
          (fun u : Fin (n + 1) → ℝ => f (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)))
          (Work.WilkG4c.pt x y)|
        = β ^ j * |Work.WilkG4c.iterDir L f (Work.WilkG4c.pt (α + β * x) y)| := by
          rw [hLp, abs_mul, abs_of_pos (pow_pos hβ0 j)]
      _ ≤ β ^ j * (2 * |Work.WilkG4c.iterDir L f
            (Work.WilkG4c.pt (α + β * x) (γs (LdirOf j M) (α + β * x)))|) :=
          mul_le_mul_of_nonneg_left hkey (pow_pos hβ0 j).le
      _ = 2 * |Work.WilkG4c.iterDir L
            (fun u : Fin (n + 1) → ℝ => f (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)))
            (Work.WilkG4c.curveFun (γ j M) x)| := by
          rw [hRp, abs_mul, abs_of_pos (pow_pos hβ0 j)]
          ring
  · intro j M x y hjm hx hxB' hy hG
    obtain ⟨hx', hxB, hGf, hGfc, hGf', hGfc'⟩ := setup j M x y hjm hx hxB' hy hG
    rw [hcurve j M x]
    exact (Work.WilkG4c.contDiffAt_affine_pullback_iff f α β (ne_of_gt hβ0)
      (Work.WilkG4c.pt x (γs (LdirOf j M) (α + β * x)))).mpr hGfc'

end Work.WilkG4c
