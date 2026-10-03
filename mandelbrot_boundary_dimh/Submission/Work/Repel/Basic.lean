import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# REPEL area: basic coordinates and the cusp conjugacy

`fam α x = e^{2πiα} x + x²` is (for `c = cOfAlpha α`) affinely conjugate to `Tc c`: the conjugacy
is the translation by `λ/2 = e^{2πiα}/2`.  Dynamical statements of Shishikura §6 are proved for
`fam α` and transported to `Tc (cOfAlpha α)` here.
-/

namespace Work.Repel

open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Topology

noncomputable section

/-- `λ = e^{2πiα}`, the multiplier at the parabolic fixed point. -/
def lam (α : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * α)

/-- The cusp family `x ↦ λ x + x²`. -/
def fam (α : ℂ) : ℂ → ℂ := fun x => lam α * x + x ^ 2

/-- The affine conjugacy `x ↦ x + λ/2`. -/
def aff (α : ℂ) : ℂ → ℂ := fun x => x + lam α / 2

lemma lam_sq (α : ℂ) : lam α ^ 2 = Complex.exp (4 * Real.pi * Complex.I * α) := by
  unfold lam
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma cOfAlpha_eq (α : ℂ) : cOfAlpha α = lam α / 2 - lam α ^ 2 / 4 := by
  rw [lam_sq]
  rfl

lemma aff_fam (α : ℂ) (x : ℂ) : Tc (cOfAlpha α) (aff α x) = aff α (fam α x) := by
  rw [cOfAlpha_eq]
  unfold Tc aff fam
  ring

lemma aff_iterate (α : ℂ) (n : ℕ) (x : ℂ) :
    (Tc (cOfAlpha α))^[n] (aff α x) = aff α ((fam α)^[n] x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ', Function.iterate_succ', Function.comp_apply, ih, aff_fam]
      rfl

/-! ## Transport of a conformal IFS along a translation -/

lemma mem_ball_add (c p : ℂ) (r : ℝ) (z : ℂ) : z ∈ ball (p + c) r ↔ z - c ∈ ball p r := by
  simp only [Metric.mem_ball, dist_eq_norm]
  rw [show z - (p + c) = (z - c) - p by ring]

lemma mem_ball_add' (c p : ℂ) (r : ℝ) (z : ℂ) : z + c ∈ ball (p + c) r ↔ z ∈ ball p r := by
  rw [mem_ball_add]
  simp

theorem isConformalIFS_shift (c : ℂ) (N : ℕ) (τ : Fin N → ℂ → ℂ) (p : ℂ) (r K : ℝ)
    (h : IsConformalIFS N τ p r K) :
    IsConformalIFS N (fun i z => τ i (z - c) + c) (p + c) r K := by
  obtain ⟨hr, hK, hdiff, hinj, hmaps, hdisj, hderiv⟩ := h
  refine ⟨hr, hK, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ((hdiff i).comp (differentiableOn_id.sub_const c)
      (fun z hz => (mem_ball_add c p r z).mp hz)).add_const c
  · intro i
    have h1 : Set.InjOn (fun z => τ i (z - c)) (ball (p + c) r) :=
      Set.InjOn.comp (hinj i) (fun a _ b _ h => sub_left_inj.mp h)
        (fun z hz => (mem_ball_add c p r z).mp hz)
    intro a ha b hb hab
    exact h1 ha hb (add_right_cancel hab)
  · intro i z hz
    have hz' : z - c ∈ ball p r := (mem_ball_add c p r z).mp hz
    have h := hmaps i hz'
    rw [mem_ball_add' c p (r / 2) (τ i (z - c))]
    exact h
  · intro i j hij
    rw [Set.disjoint_left]
    intro y hy1 hy2
    rw [Set.mem_image] at hy1 hy2
    obtain ⟨z1, hz1, hz1'⟩ := hy1
    obtain ⟨z2, hz2, hz2'⟩ := hy2
    have h1 : z1 - c ∈ ball p r := (mem_ball_add c p r z1).mp hz1
    have h2 : z2 - c ∈ ball p r := (mem_ball_add c p r z2).mp hz2
    have h3 : (fun i z => τ i (z - c) + c) i z1 = (fun i z => τ i (z - c) + c) j z2 :=
      hz1'.trans hz2'.symm
    simp only at h3
    have heq : τ i (z1 - c) = τ j (z2 - c) := add_right_cancel h3
    have hd : Disjoint (τ i '' ball p r) (τ j '' ball p r) := hdisj hij
    exact (Set.disjoint_left.mp hd) ⟨_, h1, rfl⟩ ⟨_, h2, heq.symm⟩
  · intro i z hz
    have hz' : z - c ∈ ball p (r / 2) := (mem_ball_add c p (r / 2) z).mp hz
    have hd : deriv (fun z => τ i (z - c) + c) z = deriv (τ i) (z - c) := by
      rw [show (fun z => τ i (z - c) + c) = (fun y => y + c) ∘ (fun z => τ i (z - c)) from rfl]
      rw [deriv_comp]
      · rw [deriv_comp_sub_const]
        rw [show deriv (fun y : ℂ => y + c) (τ i (z - c)) = 1 from by
          rw [deriv_add_const, deriv_id'']]
        ring
      · fun_prop
      · have hzr : z - c ∈ ball p r := by
          simp only [Metric.mem_ball, dist_eq_norm] at hz' ⊢
          linarith [hr]
        exact ((hdiff i).differentiableAt (isOpen_ball.mem_nhds hzr)).comp z
          (differentiableAt_id.sub_const c)
    rw [hd]
    exact hderiv i (z - c) hz'

/-- A word of inverse branches of `fam α` gives one of `Tc (cOfAlpha α)`. -/
theorem hypIFS_of_fam (α : ℂ) (N : ℕ) (K : ℝ)
    (h : ∃ (τ : Fin N → ℂ → ℂ) (n : Fin N → ℕ) (p : ℂ) (r : ℝ),
      IsConformalIFS N τ p r K ∧ ∀ i, 1 ≤ n i ∧ ∀ z ∈ ball p r, (fam α)^[n i] (τ i z) = z) :
    HypIFS (cOfAlpha α) N K := by
  obtain ⟨τ, n, p, r, hifs, hdyn⟩ := h
  refine ⟨fun i z => τ i (z - lam α / 2) + lam α / 2, n, p + lam α / 2, r,
    isConformalIFS_shift (lam α / 2) N τ p r K hifs, ?_⟩
  intro i
  refine ⟨(hdyn i).1, ?_⟩
  intro z hz
  have hz' : z - lam α / 2 ∈ ball p r := (mem_ball_add (lam α / 2) p r z).mp hz
  change (Tc (cOfAlpha α))^[n i] (aff α (τ i (z - lam α / 2))) = z
  rw [aff_iterate α (n i) (τ i (z - lam α / 2)), (hdyn i).2 _ hz']
  unfold aff
  ring

end

end Work.Repel
