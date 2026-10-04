import Mathlib
import Submission.Work.Diff.STE.Lead.KSBP.Defs
import Submission.Work.Diff.STE.Lead.KSBP.DiffMassDefs
import Submission.Work.Diff.STE.Lead.KSBP.exists_iteratedFDeriv_bound
import Submission.Work.Diff.STE.Lead.KSBP.tsum_le_card_mul
import Submission.Work.Diff.STE.Lead.KSBP.deriv_deriv_slice_eq
import Submission.Work.Diff.STE.Lead.KSBP.norm_dw_le_iteratedFDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `ℓ¹` mass of the second differences of a truncated coefficient family

This file proves `Work.Diff.STE.Lead.KSBP.diff_mass_le`: for a smooth, compactly supported
`ρ : ℝⁿ → ℝ` there is a constant `C` with

`∑' m : ℤⁿ, ‖diffL l (coef ρ ε) m‖ ≤ C ε^{2|l|} ε^{-n}`

for every `ε ∈ (0,1]` and every list `l` of at most `n` coordinates.

The proof has three parts.

* *Analytic.*  `diffL l (coef ρ ε) m = cdiffL l ε ρ (ε • m)` (`diffL_coef`), and the iterated
  second difference `cdiffL l ε ψ` loses a factor `ε^{2|l|}` in the uniform norm: `dw_cdiffL_le`.
  The proof is an induction on `l`: at each step one commutes the directional-derivative tower
  `dw w` past a second difference (`dw_csdiff2`) and applies the one-dimensional
  second-difference estimate `secondDiff_one_dim` to the slice, the second derivative of the slice
  being the next tick of the tower (`deriv_deriv_slice_eq`).

* *Support.*  Each second difference only samples a bounded neighbourhood of its argument, so
  `diffL l (coef ρ ε) m` vanishes as soon as one coordinate of `ε • m` is farther than `√2 + 2nε`
  from the origin (`cdiffL_eq_zero_of_ball` together with the support hypothesis `hρ0`).

* *Counting.*  Hence the sum is supported in the box `{|m_i| ≤ K}` with
  `K = ⌈(√2+2n)/ε⌉`, which has `(2K+1)^n ≤ (4n+7)^n ε^{-n}` points.
-/

set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.Lead.KSBP

variable {n : ℕ}

/-! ## Auxiliary inputs proved in sibling modules (temporary local copies) -/

theorem aux_secondDiff_one_dim {g : ℝ → ℂ} {M : ℝ} {h t : ℝ}
    (hg : ContDiff ℝ 2 g) (hM : ∀ s : ℝ, ‖deriv (deriv g) s‖ ≤ M) (hh : 0 ≤ h) :
    ‖g t - 2 * g (t - h) + g (t - 2 * h)‖ ≤ M * h ^ 2 := by
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgdd : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  -- the first difference has derivative bounded by `M * h`
  have hstep : ∀ x : ℝ, ‖deriv g x - deriv g (x - h)‖ ≤ M * h := by
    intro x
    have hconv : Convex ℝ (Set.Icc (x - h) x) := convex_Icc _ _
    have hdiff : ∀ y ∈ Set.Icc (x - h) x, DifferentiableAt ℝ (deriv g) y :=
      fun y _ => hgdd.differentiableAt
    have hbound : ∀ y ∈ Set.Icc (x - h) x, ‖deriv (deriv g) y‖ ≤ M := fun y _ => hM y
    have hxl : x - h ∈ Set.Icc (x - h) x := Set.left_mem_Icc.mpr (by linarith)
    have hxr : x ∈ Set.Icc (x - h) x := Set.right_mem_Icc.mpr (by linarith)
    have hbd := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hconv hxl hxr
    rw [show x - (x - h) = h from by ring, Real.norm_eq_abs, abs_of_nonneg hh] at hbd
    exact hbd
  -- the derivative of the first difference
  have hFderiv : ∀ x : ℝ, deriv (fun s : ℝ => g s - g (s - h)) x
      = deriv g x - deriv g (x - h) := by
    intro x
    have h2 : DifferentiableAt ℝ (fun s : ℝ => g (s - h)) x :=
      hgd.differentiableAt.comp x ((differentiableAt_id (𝕜 := ℝ) (x := x)).sub_const h)
    change deriv (g - fun s : ℝ => g (s - h)) x = deriv g x - deriv g (x - h)
    rw [deriv_sub hgd.differentiableAt h2, deriv_comp_sub_const]
  have hFd : ∀ x ∈ Set.Icc (t - h) t,
      DifferentiableAt ℝ (fun s : ℝ => g s - g (s - h)) x := by
    intro x _
    exact hgd.differentiableAt.sub (hgd.differentiableAt.comp x
      ((differentiableAt_id (𝕜 := ℝ) (x := x)).sub_const h))
  have hFb : ∀ x ∈ Set.Icc (t - h) t,
      ‖deriv (fun s : ℝ => g s - g (s - h)) x‖ ≤ M * h := by
    intro x _
    rw [hFderiv x]
    exact hstep x
  have hmem1 : t - h ∈ Set.Icc (t - h) t := Set.left_mem_Icc.mpr (by linarith)
  have hmem2 : t ∈ Set.Icc (t - h) t := Set.right_mem_Icc.mpr (by linarith)
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hFd hFb (convex_Icc _ _) hmem1 hmem2
  rw [show t - (t - h) = h from by ring, Real.norm_eq_abs, abs_of_nonneg hh] at hmain
  rw [show t - h - h = t - 2 * h from by ring] at hmain
  have hpow : M * h * h = M * h ^ 2 := by ring
  rw [hpow] at hmain
  calc ‖g t - 2 * g (t - h) + g (t - 2 * h)‖
      = ‖(g t - g (t - h)) - (g (t - h) - g (t - 2 * h))‖ := by
        congr 1; ring
    _ ≤ M * h ^ 2 := hmain

theorem aux_cdiffL_eq_zero_of_ball {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ε : ℝ) (hε : 0 ≤ ε) (l : List (Fin n)) {ψ : (Fin n → ℝ) → F} (z : Fin n → ℝ)
    (hψ : ∀ w : Fin n → ℝ, ‖w - z‖ ≤ 2 * (l.length : ℝ) * ε → ψ w = 0) :
    cdiffL l ε ψ z = 0 := by
  have aux : ∀ (l : List (Fin n)) (c : Fin n → ℝ) (R : ℝ),
      (∀ w : Fin n → ℝ, ‖w - c‖ ≤ R → ψ w = 0) →
      ∀ z' : Fin n → ℝ, ‖z' - c‖ + 2 * (l.length : ℝ) * ε ≤ R → cdiffL l ε ψ z' = 0 := by
    intro l
    induction l with
    | nil =>
        intro c R hR z' hz'
        rw [show 2 * (([] : List (Fin n)).length : ℝ) * ε = 0 by simp, add_zero] at hz'
        simpa using hR z' hz'
    | cons i l ih =>
        intro c R hR z' hz'
        have hlen : ((i :: l).length : ℝ) = (l.length : ℝ) + 1 := by
          rw [List.length_cons]; push_cast; ring
        rw [hlen] at hz'
        have hmain : ‖z' - c‖ + 2 * (l.length : ℝ) * ε + 2 * ε ≤ R := by linarith
        have h0 : cdiffL l ε ψ z' = 0 := ih c R hR z' (by linarith)
        have h1 : cdiffL l ε ψ (z' - (Pi.single i ε : Fin n → ℝ)) = 0 := by
          apply ih c R hR
          have hsh : ‖(z' - (Pi.single i ε : Fin n → ℝ)) - c‖ ≤ ‖z' - c‖ + ε := by
            calc ‖(z' - (Pi.single i ε : Fin n → ℝ)) - c‖
                = ‖(z' - c) - (Pi.single i ε : Fin n → ℝ)‖ := by
                  congr 1; abel
              _ ≤ ‖z' - c‖ + ‖(Pi.single i ε : Fin n → ℝ)‖ := norm_sub_le _ _
              _ = ‖z' - c‖ + ε := by
                  rw [Pi.norm_single, Real.norm_eq_abs, abs_of_nonneg hε]
          linarith
        have h2 : cdiffL l ε ψ (z' - (Pi.single i (2 * ε) : Fin n → ℝ)) = 0 := by
          apply ih c R hR
          have hsh : ‖(z' - (Pi.single i (2 * ε) : Fin n → ℝ)) - c‖ ≤ ‖z' - c‖ + 2 * ε := by
            calc ‖(z' - (Pi.single i (2 * ε) : Fin n → ℝ)) - c‖
                = ‖(z' - c) - (Pi.single i (2 * ε) : Fin n → ℝ)‖ := by
                  congr 1; abel
              _ ≤ ‖z' - c‖ + ‖(Pi.single i (2 * ε) : Fin n → ℝ)‖ := norm_sub_le _ _
              _ = ‖z' - c‖ + 2 * ε := by
                  rw [Pi.norm_single, Real.norm_eq_abs,
                    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * ε)]
          linarith
        rw [cdiffL_cons, csdiff2_apply, h0, h1, h2]
        simp
  refine aux l z (2 * (l.length : ℝ) * ε) (fun w hw => hψ w hw) z ?_
  simp

/-! ## The word of doubled directions -/

/-- The word `l` with every letter doubled, `[a,b] ↦ [b,b,a,a]`.  It records the two extra
directional derivatives needed when a second difference in direction `i` is pushed past the
directional-derivative tower: `wblocks (i :: l) = wblocks l ++ [i,i]`. -/
def wblocks (l : List (Fin n)) : List (Fin n) := l.foldr (fun i acc => acc ++ [i, i]) []

@[simp] lemma wblocks_nil : wblocks ([] : List (Fin n)) = [] := rfl

lemma wblocks_cons (i : Fin n) (l : List (Fin n)) : wblocks (i :: l) = wblocks l ++ [i, i] := rfl

lemma wblocks_length (l : List (Fin n)) : (wblocks l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [wblocks_cons, List.length_append, List.length_cons, List.length_nil, ih]
      ring

/-! ## Elementary facts -/

lemma smul_single_eq (h : ℝ) (i : Fin n) : h • Pi.single i (1 : ℝ) = Pi.single i h := by
  rw [← Pi.single_smul']
  simp

/-- The slice of a smooth function along a coordinate line is smooth. -/
lemma contDiff_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ψ : (Fin n → ℝ) → F} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (i : Fin n) (z : Fin n → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Ψ (z - s • Pi.single i (1 : ℝ))) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => s • (Pi.single i (1 : ℝ) : Fin n → ℝ)) :=
    contDiff_id.smul_const (Pi.single i (1 : ℝ) : Fin n → ℝ)
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => z - s • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
    have hz : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => z) := contDiff_const
    exact hz.sub h1
  exact hΨ.comp h2

/-- The second difference, expanded. -/
lemma csdiff2_apply' (Ψ : (Fin n → ℝ) → ℂ) (i : Fin n) (h : ℝ) (z : Fin n → ℝ) :
    csdiff2 i h Ψ z = Ψ z - 2 * Ψ (z - Pi.single i h) + Ψ (z - Pi.single i (2 * h)) := by
  rw [csdiff2_apply, RCLike.real_smul_eq_coe_mul]
  norm_num

/-- The combination `g (2h) - 2 g h + g 0` of the slice `g s = Ψ (z - s eᵢ)`. -/
lemma slice_comb (Ψ : (Fin n → ℝ) → ℂ) (i : Fin n) (h : ℝ) (z : Fin n → ℝ) :
    (fun s : ℝ => Ψ (z - s • Pi.single i (1 : ℝ))) (2 * h)
      - 2 * (fun s : ℝ => Ψ (z - s • Pi.single i (1 : ℝ))) h
      + (fun s : ℝ => Ψ (z - s • Pi.single i (1 : ℝ))) 0
      = Ψ z - 2 * Ψ (z - Pi.single i h) + Ψ (z - Pi.single i (2 * h)) := by
  have h2 : (2 * h) • Pi.single i (1 : ℝ) = Pi.single i (2 * h) := smul_single_eq _ _
  have h1 : h • Pi.single i (1 : ℝ) = Pi.single i h := smul_single_eq _ _
  simp only [h2, h1, zero_smul, sub_zero]
  ring

/-- The second difference as a combination of the three values of the slice
`s ↦ Ψ (z - s eᵢ)` at `0`, `h` and `2h`. -/
lemma csdiff2_eq_slice_comb (Ψ : (Fin n → ℝ) → ℂ) (i : Fin n) (h : ℝ) (z : Fin n → ℝ) :
    csdiff2 i h Ψ z = (fun s : ℝ => Ψ (z - s • Pi.single i (1 : ℝ))) (2 * h)
      - 2 * (fun s : ℝ => Ψ (z - s • Pi.single i (1 : ℝ))) h
      + (fun s : ℝ => Ψ (z - s • Pi.single i (1 : ℝ))) 0 := by
  rw [csdiff2_apply', slice_comb]

/-! ## The main analytic estimate -/

/-- **The second difference loses `ε²` per coordinate.**  For a smooth `ψ` and a word `w` of
directional derivatives, `dw w (cdiffL l ε ψ)` is bounded by `ε^{2|l|}` times the uniform bound
on the `2|l| + |w|`-fold directional derivative of `ψ` in the doubled word. -/
theorem dw_cdiffL_le (ε : ℝ) (hε : 0 ≤ ε) (l w : List (Fin n)) {ψ : (Fin n → ℝ) → ℂ} {M : ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hM : ∀ z, ‖dw (wblocks l ++ w) ψ z‖ ≤ M) :
    ∀ z, ‖dw w (cdiffL l ε ψ) z‖ ≤ ε ^ (2 * l.length) * M := by
  induction l generalizing w with
  | nil => intro z; simpa using hM z
  | cons i l ih =>
      intro z
      have hcd : ContDiff ℝ (⊤ : ℕ∞) (cdiffL l ε ψ) := contDiff_cdiffL l hψ ε
      have hdw : ContDiff ℝ (⊤ : ℕ∞) (dw w (cdiffL l ε ψ)) := contDiff_dw w hcd
      -- the hypothesis for the tail, with the word extended by the two copies of `i`
      have hM' : ∀ z, ‖dw (wblocks l ++ ([i, i] ++ w)) ψ z‖ ≤ M := by
        intro z
        have h := hM z
        rw [wblocks_cons] at h
        rwa [List.append_assoc] at h
      have ih' : ∀ z, ‖dw ([i, i] ++ w) (cdiffL l ε ψ) z‖ ≤ ε ^ (2 * l.length) * M :=
        ih ([i, i] ++ w) hM'
      -- the slice of the tower along the coordinate line through `z`
      set G : ℝ → ℂ := fun s => dw w (cdiffL l ε ψ) (z - s • Pi.single i (1 : ℝ)) with hG
      have hlev : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) := by simp
      have hGcd : ContDiff ℝ 2 G := by
        rw [hG]
        exact (contDiff_slice hdw i z).of_le hlev
      have hslice : ∀ s : ℝ, ‖deriv (deriv G) s‖ ≤ ε ^ (2 * l.length) * M := by
        intro s
        have h1 : deriv (deriv G) s
            = fderiv ℝ (fun w' => fderiv ℝ (dw w (cdiffL l ε ψ)) w' (Pi.single i (1 : ℝ)))
                (z - s • Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) := by
          rw [hG]
          exact deriv_deriv_slice_eq (dw w (cdiffL l ε ψ))
            ((contDiff_dw w hcd).of_le hlev) i z s
        rw [h1]
        change ‖(dw [i, i] (dw w (cdiffL l ε ψ))) (z - s • Pi.single i (1 : ℝ))‖
          ≤ ε ^ (2 * l.length) * M
        rw [← dw_append]
        exact ih' _
      have hmain : ‖G (2 * ε) - 2 * G ε + G 0‖ ≤ (ε ^ (2 * l.length) * M) * ε ^ 2 := by
        have h := aux_secondDiff_one_dim (g := G) (t := 2 * ε) (h := ε) hGcd hslice hε
        rwa [show (2 : ℝ) * ε - ε = ε from by ring,
             show (2 : ℝ) * ε - 2 * ε = 0 from by ring] at h
      have hconv : csdiff2 i ε (dw w (cdiffL l ε ψ)) z = G (2 * ε) - 2 * G ε + G 0 := by
        rw [csdiff2_eq_slice_comb, hG]
      rw [show dw w (cdiffL (i :: l) ε ψ) = csdiff2 i ε (dw w (cdiffL l ε ψ)) from by
            rw [cdiffL_cons, dw_csdiff2 w hcd i ε]]
      rw [hconv]
      calc ‖G (2 * ε) - 2 * G ε + G 0‖ ≤ (ε ^ (2 * l.length) * M) * ε ^ 2 := hmain
        _ = ε ^ (2 * (i :: l).length) * M := by
            rw [List.length_cons]
            ring

theorem diff_mass_le {n : ℕ} (ρ : (Fin n → ℝ) → ℝ)
    (hρ : ∀ y : Fin n → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin n → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ l : List (Fin n), l.length ≤ n →
      ∑' m : Fin n → ℤ, ‖Work.Diff.STE.Lead.KSBP.diffL l (Work.Diff.STE.Lead.KSBP.coef ρ ε) m‖
        ≤ C * ε ^ (2 * l.length) * ε⁻¹ ^ n := by
  classical
  -- the complexification of `ρ`
  set ρc : (Fin n → ℝ) → ℂ := fun y => (ρ y : ℂ) with hρc_def
  have hρc : ContDiff ℝ (⊤ : ℕ∞) ρc := by
    rw [hρc_def]
    exact Complex.ofRealCLM.contDiff.comp hρs
  have hρc0 : ∀ y : Fin n → ℝ, 2 < ∑ i, (y i) ^ 2 → ρc y = 0 := by
    intro y hy
    rw [hρc_def]
    simp [hρ0 y hy]
  -- a uniform bound on the whole Fréchet tower of `ρc`
  have hex : ∀ m : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ y : Fin n → ℝ, ‖iteratedFDeriv ℝ m ρc y‖ ≤ A :=
    fun m => exists_iteratedFDeriv_bound ρc hρc0 hρc
  let Bb : ℕ → ℝ := fun m => Classical.choose (hex m)
  have hBb : ∀ m : ℕ, 0 ≤ Bb m ∧ ∀ y : Fin n → ℝ, ‖iteratedFDeriv ℝ m ρc y‖ ≤ Bb m :=
    fun m => Classical.choose_spec (hex m)
  set A : ℝ := ∑ m ∈ Finset.range (2 * n + 1), Bb m with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun m _ => (hBb m).1
  have hAb : ∀ m ≤ 2 * n, ∀ y : Fin n → ℝ, ‖iteratedFDeriv ℝ m ρc y‖ ≤ A := by
    intro m hm y
    have h1 : Bb m ≤ A :=
      Finset.single_le_sum (fun k _ => (hBb k).1) (Finset.mem_range.mpr (by omega))
    exact le_trans ((hBb m).2 y) h1
  refine ⟨((4 * (n : ℝ) + 7) ^ n) * A, by positivity, ?_⟩
  intro ε hε l hl
  have hε0 : 0 ≤ ε := le_of_lt hε.1
  have hε1 : ε ≤ 1 := hε.2
  -- the pointwise bound on the second-difference mass
  have hpoint : ∀ m : Fin n → ℤ, ‖diffL l (coef ρ ε) m‖ ≤ ε ^ (2 * l.length) * A := by
    intro m
    rw [diffL_coef ρ ε l m]
    refine dw_cdiffL_le ε hε0 l [] hρc (fun z => ?_) (sm ε m)
    rw [List.append_nil]
    have h1 : ‖dw (wblocks l) ρc z‖ ≤ ‖iteratedFDeriv ℝ (2 * l.length) ρc z‖ := by
      have h := norm_dw_le_iteratedFDeriv (F := ℂ) (wblocks l) hρc z
      rwa [wblocks_length] at h
    exact le_trans h1 (hAb (2 * l.length) (by omega) z)
  -- the support box
  set K : ℕ := Nat.ceil ((Real.sqrt 2 + 2 * (n : ℝ)) / ε) with hK
  have hKle : (Real.sqrt 2 + 2 * (n : ℝ)) / ε ≤ (K : ℝ) := Nat.le_ceil _
  have hsupp : ∀ m : Fin n → ℤ, ‖diffL l (coef ρ ε) m‖ ≠ 0 →
      ∀ i : Fin n, |m i| ≤ (K : ℤ) := by
    intro m hm i
    by_contra hcon
    -- `K` is smaller than the `i`-th coordinate of `m`
    have hltR : (K : ℝ) < |((m i : ℤ) : ℝ)| := by
      rcases (lt_abs.mp (lt_of_not_ge hcon)) with h | h
      · have h' : (K : ℝ) < ((m i : ℤ) : ℝ) := by exact_mod_cast h
        linarith [le_abs_self (((m i : ℤ) : ℝ))]
      · have h' : (K : ℝ) < -((m i : ℤ) : ℝ) := by exact_mod_cast h
        linarith [neg_le_abs (((m i : ℤ) : ℝ))]
    -- the corresponding coordinate of `ε • m` is farther than `√2 + 2nε`
    have hfar : Real.sqrt 2 + 2 * (n : ℝ) < |(sm ε m) i| := by
      have h1 : (Real.sqrt 2 + 2 * (n : ℝ)) / ε < |((m i : ℤ) : ℝ)| :=
        lt_of_le_of_lt hKle hltR
      have h2 : ε * ((Real.sqrt 2 + 2 * (n : ℝ)) / ε) < ε * |((m i : ℤ) : ℝ)| :=
        mul_lt_mul_of_pos_left h1 hε.1
      rw [mul_div_cancel₀ _ (ne_of_gt hε.1)] at h2
      rw [← abs_of_pos hε.1, ← abs_mul] at h2
      simpa [sm] using h2
    -- `ρc` vanishes on the ball of radius `2 |l| ε` around `ε • m`
    have hball : ∀ w : Fin n → ℝ, ‖w - sm ε m‖ ≤ 2 * (l.length : ℝ) * ε → ρc w = 0 := by
      intro w hw
      apply hρc0
      have hdist : |w i - (sm ε m) i| ≤ 2 * (l.length : ℝ) * ε := by
        have h1 : |w i - (sm ε m) i| ≤ ‖w - sm ε m‖ := by
          simpa [Pi.sub_apply] using norm_le_pi_norm (w - sm ε m) i
        exact le_trans h1 hw
      have hlR : (l.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast hl
      have hdist' : |w i - (sm ε m) i| ≤ 2 * (n : ℝ) * ε := by
        have hl2 : 2 * (l.length : ℝ) ≤ 2 * (n : ℝ) := by linarith [hlR]
        exact le_trans hdist (mul_le_mul_of_nonneg_right hl2 (le_of_lt hε.1))
      have hwi : Real.sqrt 2 < |w i| := by
        have h3 : |(sm ε m) i| ≤ |w i| + |w i - (sm ε m) i| := by
          have hEq : ((sm ε m) i - w i) + w i = (sm ε m) i := sub_add_cancel _ _
          calc |(sm ε m) i| = |((sm ε m) i - w i) + w i| := by rw [hEq]
            _ ≤ |(sm ε m) i - w i| + |w i| := abs_add_le _ _
            _ = |w i - (sm ε m) i| + |w i| := by rw [abs_sub_comm]
            _ = |w i| + |w i - (sm ε m) i| := by rw [add_comm]
        have hfac : 2 * (n : ℝ) * ε ≤ 2 * (n : ℝ) :=
          mul_le_of_le_one_right (by positivity) hε1
        linarith [hfar, h3, hdist', hfac]
      have h2 : 2 < (w i) ^ 2 := by
        rw [← sq_abs]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, hwi]
      have h3 := Finset.single_le_sum (f := fun j : Fin n => (w j) ^ 2)
        (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
      linarith
    have hzero : cdiffL l ε ρc (sm ε m) = 0 :=
      aux_cdiffL_eq_zero_of_ball ε hε0 l (sm ε m) hball
    have hdl : diffL l (coef ρ ε) m = 0 := by
      rw [diffL_coef ρ ε l m]
      exact hzero
    exact hm (by rw [hdl]; simp)
  -- counting the lattice points
  have hC := tsum_le_card_mul (K := K) (f := fun m : Fin n → ℤ => ‖diffL l (coef ρ ε) m‖)
    (B := ε ^ (2 * l.length) * A) hsupp hpoint
  refine le_trans hC ?_
  have hKb : (2 * (K : ℝ) + 1) * ε ≤ 4 * (n : ℝ) + 7 := by
    have hceil : (K : ℝ) < (Real.sqrt 2 + 2 * (n : ℝ)) / ε + 1 :=
      Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (Real.sqrt 2 + 2 * (n : ℝ)) / ε by positivity)
    have hmul : (2 * (K : ℝ) + 1) * ε
        < (2 * ((Real.sqrt 2 + 2 * (n : ℝ)) / ε + 1) + 1) * ε :=
      mul_lt_mul_of_pos_right (by linarith) hε.1
    have hsimpl : (2 * ((Real.sqrt 2 + 2 * (n : ℝ)) / ε + 1) + 1) * ε
        = 2 * Real.sqrt 2 + 4 * (n : ℝ) + 3 * ε := by
      have hne : ε ≠ 0 := ne_of_gt hε.1
      have h1 : (2 * ((Real.sqrt 2 + 2 * (n : ℝ)) / ε + 1) + 1)
          = 2 * (Real.sqrt 2 + 2 * (n : ℝ)) / ε + 3 := by ring
      rw [h1, add_mul, div_mul_cancel₀ _ hne]
      ring
    have hs2 : 2 * Real.sqrt 2 ≤ 4 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    linarith [hmul, hsimpl, hs2, hε1]
  have hKb' : (2 * (K : ℝ) + 1) ≤ (4 * (n : ℝ) + 7) * ε⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hε.1]
    exact hKb
  have hpow : (2 * (K : ℝ) + 1) ^ n ≤ ((4 * (n : ℝ) + 7) * ε⁻¹) ^ n :=
    pow_le_pow_left₀ (by positivity) hKb' n
  calc (2 * (K : ℝ) + 1) ^ n * (ε ^ (2 * l.length) * A)
      ≤ ((4 * (n : ℝ) + 7) * ε⁻¹) ^ n * (ε ^ (2 * l.length) * A) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = ((4 * (n : ℝ) + 7) ^ n * A) * ε ^ (2 * l.length) * ε⁻¹ ^ n := by
        rw [mul_pow]; ring

end Work.Diff.STE.Lead.KSBP
