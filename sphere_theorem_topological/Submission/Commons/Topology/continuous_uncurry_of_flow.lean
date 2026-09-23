import Mathlib.Algebra.CharP.Defs
import Mathlib.Topology.Algebra.Ring.Real

namespace Commons.Topology

theorem continuous_uncurry_of_flow {M : Type*} [TopologicalSpace M] {φ : M → ℝ → M} {ε : ℝ}
    (hε : 0 < ε) (h0 : ∀ x : M, φ x 0 = x)
    (hadd : ∀ x : M, ∀ s t : ℝ, φ (φ x s) t = φ x (s + t))
    (hloc : ∀ x : M, ∀ t : ℝ, |t| < ε → ContinuousAt (fun p : M × ℝ => φ p.1 p.2) (x, t)) :
    Continuous (fun p : M × ℝ => φ p.1 p.2) := by
  -- Step 1: for |a| < ε, the map x ↦ φ x a is continuous.
  have hcont_par : ∀ a : ℝ, |a| < ε → Continuous (fun x : M => φ x a) := by
    intro a ha
    rw [continuous_iff_continuousAt]
    intro x
    have h2 : ContinuousAt (fun x : M => (x, a)) x := continuousAt_id.prodMk continuousAt_const
    have h3 : ContinuousAt ((fun p : M × ℝ => φ p.1 p.2) ∘ (fun x : M => (x, a))) x :=
      (hloc x a ha).comp (f := fun y : M => (y, a)) (x := x) h2
    simpa only [Function.comp_def] using h3
  -- Step 2: iterate formula  φ x (n * a) = (Φ_a)^[n] x.
  have hiter : ∀ (n : ℕ) (a : ℝ) (x : M),
      φ x ((n : ℝ) * a) = (fun y : M => φ y a)^[n] x := by
    intro n
    induction n with
    | zero =>
        intro a x
        simp [h0]
    | succ k ih =>
        intro a x
        have h1 : ((k + 1 : ℕ) : ℝ) * a = (k : ℝ) * a + a := by push_cast; ring
        rw [h1, ← hadd x ((k : ℝ) * a) a, ih a x, Function.iterate_succ_apply']
  -- Step 3: continuity in the space variable for every fixed time.
  have hcont_fixed : ∀ t : ℝ, Continuous (fun x : M => φ x t) := by
    intro t
    obtain ⟨n, hn⟩ := exists_nat_gt (max (|t| / ε) 1)
    have hgt1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hgt1.le
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hpos
    have hlt_t : |t| / ε < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    set a := t / (n : ℝ) with ha
    have hna : |a| < ε := by
      rw [ha, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
      have h' : |t| < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hlt_t
      rw [mul_comm] at h'
      exact h'
    have hnt : (n : ℝ) * a = t := by
      rw [ha, mul_comm, div_mul_cancel₀ _ hn0]
    have heq : (fun x : M => φ x t) = (fun y : M => φ y a)^[n] := by
      funext x
      rw [← hnt]
      exact hiter n a x
    rw [heq]
    exact (hcont_par a hna).iterate n
  -- Step 4: assemble joint continuity.
  rw [continuous_iff_continuousAt]
  rintro ⟨x, t⟩
  have hΦ : ContinuousAt (fun p : M × ℝ => φ p.1 p.2) (φ x t, 0) :=
    hloc (φ x t) 0 (by simpa using hε)
  have hJ : Continuous (fun p : M × ℝ => (φ p.1 t, p.2 - t)) :=
    ((hcont_fixed t).comp continuous_fst).prodMk (continuous_snd.sub continuous_const)
  set J : M × ℝ → M × ℝ := fun p => (φ p.1 t, p.2 - t) with hJdef
  have hJx : J (x, t) = (φ x t, 0) := by
    simp [hJdef]
  have hΦ' : ContinuousAt (fun p : M × ℝ => φ p.1 p.2) (J (x, t)) := by
    rw [hJx]; exact hΦ
  have hcomp : ContinuousAt ((fun p : M × ℝ => φ p.1 p.2) ∘ J) (x, t) :=
    hΦ'.comp (f := J) (x := (x, t)) hJ.continuousAt
  have key : (fun p : M × ℝ => φ p.1 p.2) ∘ J = (fun p : M × ℝ => φ p.1 p.2) := by
    funext p
    simp only [Function.comp_apply, hJdef]
    rw [hadd p.1 t (p.2 - t)]
    congr 1
    ring
  rw [key] at hcomp
  exact hcomp

end Commons.Topology