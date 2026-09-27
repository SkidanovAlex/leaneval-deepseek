import Mathlib

namespace Work.Drive

/-- The `k`-th derivative in the second variable of a `C^∞` function of two variables,
evaluated at `0`, is `C^∞` as a function of the first variable. -/
theorem contDiff_iteratedDeriv_fst {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : X × ℝ → E}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (k : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : X => iteratedDeriv k (fun t : ℝ => f (x, t)) 0) := by
  -- Stronger statement: the `k`-th derivative in the second variable is `C^∞`
  -- jointly in both variables.
  have key : ∀ k : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : X × ℝ => iteratedDeriv k (fun s : ℝ => f (p.1, s)) p.2) := by
    intro k
    induction k with
    | zero =>
      simpa [iteratedDeriv_zero] using hf
    | succ k ih =>
      -- `(x, t) ↦ iteratedDeriv k (fun s => f (x, s)) t` is smooth jointly in `(x, t)`.
      have hmap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : (X × ℝ) × ℝ => ((q.1.1, q.2) : X × ℝ)) := by
        exact (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
      -- hence the curried version is smooth, so `ContDiff.fderiv_apply` applies.
      have hunc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (Function.uncurry
            (fun p : X × ℝ => fun s : ℝ => iteratedDeriv k (fun s' : ℝ => f (p.1, s')) s)) := by
        convert ih.comp hmap using 1
        ext q
        rfl
      have hle : (((⊤ : ℕ∞) : WithTop ℕ∞) + 1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        simp
      -- the derivative in the second variable of the `k`-th derivative.
      have h := hunc.fderiv_apply (g := fun p : X × ℝ => p.2) (k := fun _ => (1 : ℝ))
          (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) contDiff_snd contDiff_const hle
      rw [show (fun p : X × ℝ =>
              (fderiv ℝ ((fun p : X × ℝ =>
                fun s : ℝ => iteratedDeriv k (fun s' : ℝ => f (p.1, s')) s) p) p.2) 1)
          = (fun p : X × ℝ => iteratedDeriv (k + 1) (fun s : ℝ => f (p.1, s)) p.2) from by
        funext p
        show (fderiv ℝ (fun s : ℝ => iteratedDeriv k (fun s' : ℝ => f (p.1, s')) s) p.2) 1 = _
        rw [iteratedDeriv_succ]
        rfl] at h
      exact h
  have hfin := key k |>.comp (contDiff_id.prodMk
    (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun _ : X => (0 : ℝ)))
  convert hfin using 1
  ext x
  rfl

end Work.Drive
