import Mathlib

open scoped ContDiff

namespace Work.Drive.N2

/-- If a one-parameter group `FL` of self-maps of a real normed space `E` is jointly `C^∞` on a
neighbourhood `(-1,1) × E` of the time-zero slice and each of its small-time slices is `C^∞`, then
it is jointly `C^∞` on all of `ℝ × E`.

The proof is the standard local-to-global argument for flows: the semigroup law turns smoothness
near time `0` into smoothness everywhere. -/
theorem jointFlowAssembly {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (FL : ℝ → E → E)
    (h0 : ∀ p, FL 0 p = p) (hsem : ∀ s t p, FL (s + t) p = FL s (FL t p))
    (hslice : ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| ≤ δ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL s))
    (hlocal : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => FL p.1 p.2)
      (Set.Ioo (-1) 1 ×ˢ (Set.univ : Set E))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => FL p.1 p.2) := by
  -- Step 1: every time-slice `FL s` is `C^∞`.  Writing `s = N * (s/N)` with `N` large enough
  -- that `|s/N| ≤ δ`, the semigroup law gives `FL s = (FL (s/N))^[N]`, and a `C^∞` map is
  -- `C^∞` under iteration.
  have hFL : ∀ s : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL s) := by
    intro s
    obtain ⟨δ, hδpos, hδ⟩ := hslice
    have hex : ∃ N : ℕ, 0 < N ∧ |s| / (N:ℝ) ≤ δ := by
      obtain ⟨m, hm⟩ := exists_nat_ge (|s| / δ)
      refine ⟨m+1, Nat.succ_pos m, ?_⟩
      rw [div_le_iff₀ (by exact_mod_cast (Nat.succ_pos m : 0 < m+1))]
      have hm' : |s| ≤ (m:ℝ) * δ := (div_le_iff₀ hδpos).mp hm
      have hcast : (m:ℝ) ≤ ((m+1:ℕ):ℝ) := by push_cast; linarith
      have h1 := mul_le_mul_of_nonneg_right hcast (le_of_lt hδpos)
      linarith
    obtain ⟨N, hNpos, hle⟩ := hex
    have hNne : (N:ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
    have hNcastpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
    have ht : |s / (N:ℝ)| ≤ δ := by
      rw [abs_div, abs_of_nonneg (le_of_lt hNcastpos)]
      exact hle
    have hsmall : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (FL (s / (N:ℝ))) := hδ _ ht
    have hiterfun : ∀ k : ℕ, (FL (s / (N:ℝ)))^[k] = FL ((k:ℝ) * (s / (N:ℝ))) := by
      intro k
      induction k with
      | zero => funext p; simp [h0]
      | succ k ih =>
        rw [Function.iterate_succ', ih]
        funext p
        simp only [Function.comp_apply]
        rw [← hsem (s / (N:ℝ)) ((k:ℝ) * (s / (N:ℝ))) p]
        congr 1
        push_cast
        ring
    have hcd_iter : ∀ k : ℕ, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) ((FL (s / (N:ℝ)))^[k]) := by
      intro k
      induction k with
      | zero => simpa [Function.iterate_zero] using
          (contDiff_id : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (id : E → E))
      | succ k ih => rw [Function.iterate_succ']; exact hsmall.comp ih
    have hmul : (N:ℝ) * (s / (N:ℝ)) = s := mul_div_cancel₀ s hNne
    have hiterN : ((FL (s / (N:ℝ)))^[N]) = FL s := by
      rw [hiterfun N, hmul]
    rw [← hiterN]
    exact hcd_iter N
  -- Step 2: joint smoothness at an arbitrary point `(s₀, p₀)`.  The semigroup law gives the
  -- identity `FL s p = FL s₀ (FL (s - s₀) p)`, i.e. the joint map is the composition of the
  -- (globally `C^∞`) map `FL s₀` with the jointly smooth map `(s,p) ↦ FL (s - s₀) p`.
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨s₀, p₀⟩ := x
  have hJ0 : ContDiffAt ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun p : ℝ × E => FL p.1 p.2) (0, p₀) :=
    hlocal.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨by constructor <;> norm_num, trivial⟩)
  have hJ : ContDiffAt ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun p : ℝ × E => FL p.1 p.2) (s₀ - s₀, p₀) := by
    have he : (s₀ - s₀, p₀) = (0, p₀) := by simp
    rw [he]; exact hJ0
  have hA : ContDiffAt ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun q : ℝ × E => FL (q.1 - s₀) q.2) (s₀, p₀) := by
    have hτ : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun q : ℝ × E => (q.1 - s₀, q.2)) := by fun_prop
    exact ContDiffAt.comp (s₀, p₀) hJ hτ.contDiffAt
  have hB : ContDiffAt ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun q : ℝ × E => FL s₀ (FL (q.1 - s₀) q.2)) (s₀, p₀) :=
    ContDiff.comp_contDiffAt (s₀, p₀) (hFL s₀) hA
  have hfun : (fun p : ℝ × E => FL p.1 p.2) = fun q : ℝ × E => FL s₀ (FL (q.1 - s₀) q.2) := by
    funext q
    show FL q.1 q.2 = FL s₀ (FL (q.1 - s₀) q.2)
    rw [← hsem s₀ (q.1 - s₀) q.2]
    congr 1
    ring
  rw [hfun]
  exact hB

end Work.Drive.N2
