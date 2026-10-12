import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.FarQ3Core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped BigOperators

namespace Work.BoseFixR

open Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {L : Type*} [AddCommGroup L] [Fintype L] [DecidableEq L]

/-! ## 1. The window package (the θ-mode count and the number bounds) -/

/-- `⟨f, n_k f⟩ = ‖a_kf‖²`. -/
private lemma qw_nOp_self (F : FockData L) (k : L) (f : F.H) :
    F.qw f (F.nOp k) = F.bp (F.a k f) (F.a k f) := by
  rw [FockData.qw]
  simp only [FockData.nOp, LinearMap.comp_apply, F.aDag_adjoint]

/-- **The θ-mode count**: `Σ_{s∈S}‖ã_sg‖² ≤ ⟨n₊g, g⟩` for a finite family of excited
θ-modes (the operator form of the count is the field `TildeData.ta_le_N`). -/
private lemma ta_sum_le (F : FockData L) (T : TildeData F) (S : Finset L)
    (hS : ∀ s ∈ S, s ≠ 0) (g : F.H) :
    ∑ s ∈ S, F.bp (T.ta s g) (T.ta s g) ≤ F.bp (T.N g) g := by
  have h1 : (∑ s ∈ S, T.taDag s ∘ₗ T.ta s) g = ∑ s ∈ S, T.taDag s (T.ta s g) := by
    have h0 : (∑ s ∈ S, T.taDag s ∘ₗ T.ta s)
        = ∑ s ∈ S, (1 : ℝ) • (T.taDag s ∘ₗ T.ta s) := by simp
    rw [h0, sum_smul_apply_zp]
    simp only [one_smul, LinearMap.comp_apply]
  calc ∑ s ∈ S, F.bp (T.ta s g) (T.ta s g)
      = F.bp ((∑ s ∈ S, T.taDag s ∘ₗ T.ta s) g) g := by
        rw [h1, bp_sum_zp]
        exact Finset.sum_congr rfl fun s _ => (T.taDag_adjoint s (T.ta s g) g).symm
    _ ≤ F.bp (T.N g) g := T.ta_le_N S hS g

/-- The shift sum over a finite mode set is dominated by the sum over all modes: the
map `k ↦ s - k` is injective. -/
private lemma sum_shift_le (K : Finset L) (Y : L → ℝ) (hY : ∀ p : L, 0 ≤ Y p) (s : L) :
    ∑ k ∈ K, Y (s - k) ≤ ∑ p : L, Y p := by
  have hinj : Set.InjOn (fun k : L => s - k) ↑K := by
    intro k _ k' _ h
    exact sub_right_inj.mp h
  rw [← Finset.sum_image (f := Y) (g := fun k : L => s - k) hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hY p)

/-- **The number package on FS's window.**  For `f = 1_{[0,𝓜]}(n₊)f` (`T.NWindow 𝓜 f`)
and the diagonal hypothesis `Σ_p⟨n_pg,g⟩ ≤ 16⟨n₊g,g⟩`: the window value
`⟨n₊f,f⟩ ≤ 𝓜‖f‖²`, the θ-mode count `Σ_s‖ã_sf‖² ≤ 𝓜‖f‖²`, the particle count
`Σ_p‖a_pf‖² ≤ 16𝓜‖f‖²`, and its `n₊`-weighted version
`Σ_p⟨a_pf, n₊(a_pf)⟩ ≤ 16𝓜²‖f‖²` (each `a_pf` lies in the window by the lowering
grading `[n₊,a_p] = -a_p`). -/
private lemma numWind (F : FockData L) (T : TildeData F) {M : ℝ} (hM : 0 ≤ M) (f : F.H)
    (hwin : T.NWindow M f)
    (hnN : ∀ g : F.H, ∑ p : L, F.bp (F.nOp p g) g ≤ 16 * F.bp (T.N g) g) :
    F.bp (T.N f) f ≤ M * F.normSq f ∧
    (∑ s ∈ Work.BoseB7.excited L, F.bp (T.ta s f) (T.ta s f) ≤ M * F.normSq f) ∧
    (∑ p : L, F.bp (F.a p f) (F.a p f) ≤ 16 * M * F.normSq f) ∧
    (∑ p : L, F.bp (F.a p f) (T.N (F.a p f)) ≤ 16 * M ^ 2 * F.normSq f) := by
  have hexc : ∀ s ∈ Work.BoseB7.excited L, s ≠ 0 := fun s hs => (Finset.mem_erase.mp hs).1
  have hNf : F.bp (T.N f) f ≤ M * F.normSq f := NWindow_bp_N_le F T hM hwin
  have hta : ∑ s ∈ Work.BoseB7.excited L, F.bp (T.ta s f) (T.ta s f) ≤ M * F.normSq f :=
    NWindow_ta_sum F T hM hwin (Work.BoseB7.excited L) hexc
  have han : ∑ p : L, F.bp (F.a p f) (F.a p f) ≤ 16 * M * F.normSq f := by
    have h1 : ∑ p : L, F.bp (F.nOp p f) f ≤ 16 * F.bp (T.N f) f := hnN f
    have h2 : ∑ p : L, F.bp (F.nOp p f) f = ∑ p : L, F.bp (F.a p f) (F.a p f) :=
      Finset.sum_congr rfl fun p _ => by
        rw [FockData.nOp, LinearMap.comp_apply, F.aDag_adjoint]
    rw [h2] at h1
    calc ∑ p : L, F.bp (F.a p f) (F.a p f) ≤ 16 * F.bp (T.N f) f := h1
      _ ≤ 16 * (M * F.normSq f) :=
          mul_le_mul_of_nonneg_left hNf (show (0 : ℝ) ≤ 16 by norm_num)
      _ = 16 * M * F.normSq f := by ring
  have hY : ∑ p : L, F.bp (F.a p f) (T.N (F.a p f)) ≤ 16 * M ^ 2 * F.normSq f := by
    have hterm : ∀ p : L, F.bp (F.a p f) (T.N (F.a p f)) ≤ M * F.bp (F.a p f) (F.a p f) := by
      intro p
      have hw : T.NWindow M (F.a p f) := T.NWindow_a p hwin
      have h := NWindow_bp_N_le F T hM hw
      rw [F.bp_symm (F.a p f) (T.N (F.a p f))]
      simpa only [FockData.normSq] using h
    calc ∑ p : L, F.bp (F.a p f) (T.N (F.a p f))
        ≤ ∑ p : L, M * F.bp (F.a p f) (F.a p f) := Finset.sum_le_sum fun p _ => hterm p
      _ = M * ∑ p : L, F.bp (F.a p f) (F.a p f) := (Finset.mul_sum _ _ _).symm
      _ ≤ M * (16 * M * F.normSq f) := mul_le_mul_of_nonneg_left han hM
      _ = 16 * M ^ 2 * F.normSq f := by ring
  exact ⟨hNf, hta, han, hY⟩

/-! ## 2. The commutator expansion of the shift state -/

/-- **The pairing identity with the box commutator.**  Since `a_p†` is the adjoint of
`a_p` and `[a_p,a_q†] = ccrK p q`,

  `⟨a_p†g, a_q†g'⟩ = ⟨a_q g, a_p g'⟩ + ccrK p q·⟨g,g'⟩`.

The crossing of the two modes is what produces the shifted kernel `ccrK (s−k)(s'−k)`
of the hypothesis `hccrB`. -/
private lemma bp_aDag_aDag (F : FockData L) (p q : L) (g g' : F.H) :
    F.bp (F.aDag p g) (F.aDag q g')
      = F.bp (F.a q g) (F.a p g') + F.ccrK p q * F.bp g g' := by
  have h2 : F.a p (F.aDag q g') = F.aDag q (F.a p g') + F.ccrK p q • g' := by
    have h := LinearMap.congr_fun (F.ccr p q) g'
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] at h
    exact h
  rw [F.aDag_adjoint p g (F.aDag q g'), h2, map_add, map_smul, smul_eq_mul,
    F.bp_symm g (F.aDag q (F.a p g')), F.aDag_adjoint q (F.a p g') g,
    F.bp_symm (F.a p g') (F.a q g)]

/-- The double sum is invariant under swapping the two summation indices. -/
private lemma sum_swap₂ (S : Finset L) (f : L → L → ℝ) :
    (∑ s ∈ S, ∑ s' ∈ S, f s' s) = ∑ s ∈ S, ∑ s' ∈ S, f s s' := by
  rw [Finset.sum_comm]

/-- **The AM–GM/relabelling bound for a double sum of Fock pairings.**  If the second
family is the first with the indices interchanged (`Y s s' = X s' s`), then

  `Σ_{s,s'} c_sc_{s'}⟨X_{ss'}, Y_{ss'}⟩ ≤ Σ_{s,s'} |c_s||c_{s'}|⟨X_{ss'},X_{ss'}⟩`.

Termwise `⟨X,Y⟩ ≤ |⟨X,Y⟩| ≤ (⟨X,X⟩+⟨Y,Y⟩)/2` (`SumABound.bp_abs_le`); summing, the
`Y`-half is the `X`-half by the relabelling `s ↔ s'` (`sum_swap₂`) and `|c_sc_{s'}| =
|c_{s'}c_s|`. -/
private lemma double_sum_amgm (F : FockData L) (S : Finset L) (c : L → ℝ)
    (X Y : L → L → F.H) (hY : ∀ s s', Y s s' = X s' s) :
    ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * F.bp (X s s') (Y s s')
      ≤ ∑ s ∈ S, ∑ s' ∈ S, |c s| * |c s'| * F.bp (X s s') (X s s') := by
  have hterm : ∀ s ∈ S, ∀ s' ∈ S,
      c s * c s' * F.bp (X s s') (Y s s')
        ≤ |c s| * |c s'| * ((F.bp (X s s') (X s s') + F.bp (Y s s') (Y s s')) / 2) := by
    intro s _ s' _
    have h2 : |F.bp (X s s') (Y s s')| ≤
        (F.bp (X s s') (X s s') + F.bp (Y s s') (Y s s')) / 2 :=
      Work.BoseB7.SumABound.bp_abs_le F _ _
    calc c s * c s' * F.bp (X s s') (Y s s')
        ≤ |c s * c s' * F.bp (X s s') (Y s s')| := le_abs_self _
      _ = |c s| * |c s'| * |F.bp (X s s') (Y s s')| := by rw [abs_mul, abs_mul]
      _ ≤ |c s| * |c s'| * ((F.bp (X s s') (X s s') + F.bp (Y s s') (Y s s')) / 2) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hEeq : (∑ s ∈ S, ∑ s' ∈ S, |c s| * |c s'| * F.bp (Y s s') (Y s s'))
      = (∑ s ∈ S, ∑ s' ∈ S, |c s| * |c s'| * F.bp (X s s') (X s s')) := by
    calc ∑ s ∈ S, ∑ s' ∈ S, |c s| * |c s'| * F.bp (Y s s') (Y s s')
        = ∑ s ∈ S, ∑ s' ∈ S, |c s| * |c s'| * F.bp (X s' s) (X s' s) := by
          refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun s' _ => ?_))
          rw [hY s s']
      _ = ∑ s ∈ S, ∑ s' ∈ S, |c s| * |c s'| * F.bp (X s s') (X s s') := by
          have hf := sum_swap₂ S (fun a b => |c a| * |c b| * F.bp (X b a) (X b a))
          have hA : (∑ s ∈ S, ∑ s' ∈ S, |c s'| * |c s| * F.bp (X s s') (X s s'))
              = ∑ s ∈ S, ∑ s' ∈ S, |c s| * |c s'| * F.bp (X s s') (X s s') := by
            refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun s' _ => ?_))
            ring
          exact hf.symm.trans hA
  have hDdiv : (∑ s ∈ S, ∑ s' ∈ S,
        |c s| * |c s'| * ((F.bp (X s s') (X s s') + F.bp (Y s s') (Y s s')) / 2))
      = (∑ s ∈ S, ∑ s' ∈ S, |c s| * |c s'| * F.bp (X s s') (X s s') / 2)
        + (∑ s ∈ S, ∑ s' ∈ S, |c s| * |c s'| * F.bp (Y s s') (Y s s') / 2) := by
    have h1 : ∀ s ∈ S, ∀ s' ∈ S,
        |c s| * |c s'| * ((F.bp (X s s') (X s s') + F.bp (Y s s') (Y s s')) / 2)
          = |c s| * |c s'| * F.bp (X s s') (X s s') / 2
            + |c s| * |c s'| * F.bp (Y s s') (Y s s') / 2 := by
      intro s _ s' _; ring
    rw [Finset.sum_congr rfl (fun s hs => Finset.sum_congr rfl (fun s' hs' => h1 s hs s' hs'))]
    simp only [Finset.sum_add_distrib]
  have hpullX : (∑ s ∈ S, ∑ s' ∈ S, |c s| * |c s'| * F.bp (X s s') (X s s') / 2)
      = (∑ s ∈ S, ∑ s' ∈ S, |c s| * |c s'| * F.bp (X s s') (X s s')) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.sum_div]
  have hpullY : (∑ s ∈ S, ∑ s' ∈ S, |c s| * |c s'| * F.bp (Y s s') (Y s s') / 2)
      = (∑ s ∈ S, ∑ s' ∈ S, |c s| * |c s'| * F.bp (Y s s') (Y s s')) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.sum_div]
  refine le_trans (Finset.sum_le_sum (fun s hs => Finset.sum_le_sum (fun s' hs' =>
    hterm s hs s' hs'))) ?_
  rw [hDdiv, hpullX, hpullY, hEeq]
  linarith

/-- `ã_s` commutes with every `a_p` (`TildeData.ta_a_comm`), in the form needed for the
pairing `⟨a_pã_sf, a_pã_sf⟩ = ⟨ã_s a_pf, ã_s a_pf⟩`. -/
private lemma bp_ta_a (F : FockData L) (T : TildeData F) (s p : L) (f : F.H) :
    F.bp (F.a p (T.ta s f)) (F.a p (T.ta s f))
      = F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f)) := by
  have h := LinearMap.congr_fun (T.ta_a_comm s p) f
  simp only [LinearMap.comp_apply] at h
  rw [← h]

/-! ## 3. The wedge bound -/

theorem Q3TWedgeBoundV2 {L : Type*} [AddCommGroup L] [Fintype L] [DecidableEq L]
    (F : Work.BoseB7.FockData L) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env L)
    {ε Cf Row M : ℝ} (f : F.H) (hε : 0 < ε) (hCf : 0 ≤ Cf) (hRow : 0 ≤ Row) (hM : 0 ≤ M)
    (haSc : 0 < E.aScat) (hKH : 0 < E.KH)
    (hfl1 : ∀ s : L, |E.fL s| ≤ 1)
    (hcfs : ∑ s ∈ Work.BoseB7.excited L, |E.fL s| ≤ Cf)
    (hW1 : ∀ k : L, |E.W1 k| ≤ 16 * Real.pi * E.aScat)
    (hPH : ∀ k ∈ F.PHset E, 1 / (2 * E.KH * E.aScat) ≤ ‖F.kmom k‖)
    (hRowE : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 ≤ Row)
    (hccrB : ∀ (k : L) (c : L → ℝ) (u : L → F.H),
      ∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
          c s * c s' * F.ccrK (s - k) (s' - k) * F.bp (u s) (u s')
        ≤ 100 * ∑ s ∈ Work.BoseB7.excited L, c s ^ 2 * F.bp (u s) (u s))
    (hnN : ∀ g : F.H, ∑ p : L, F.bp (F.nOp p g) g ≤ 16 * F.bp (T.N g) g)
    (hτ0 : ∀ k : L, 0 ≤ E.tau k) (hτeven : ∀ k : L, E.tau (-k) = E.tau k)
    (hτge : ∀ k : L, F.PH E.KH E.aScat k → ‖F.kmom k‖ ^ 2 / 2 ≤ E.tau k)
    (hwin : T.NWindow M f) :
    -(2 / ε) * (E.z / E.ell ^ 3) ^ 2
        * (Cf * (2000 * (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * M ^ 2)
            + 2000 * Row * M) * F.normSq f
      ≤ F.qw f (T.Q3T E) + F.qw f (∑ k : L, (ε * E.tau k) • F.nOp k) := by
  obtain ⟨hNf, hTasum, hAsum, hYsum⟩ := numWind F T hM f hwin hnN
  -- ### 0. bookkeeping: positive momentum, the pointwise weight, nonnegativities
  have hkp : ∀ k ∈ F.PHset E, 0 < ‖F.kmom k‖ := by
    intro k hk
    have h1 : (0 : ℝ) < 1 / (2 * E.KH * E.aScat) := by positivity
    exact lt_of_lt_of_le h1 (hPH k hk)
  have hwle : ∀ k ∈ F.PHset E,
      E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 ≤ (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 := by
    intro k hk
    have hW : E.W1 k ^ 2 ≤ (16 * Real.pi * E.aScat) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (E.W1 k)) (hW1 k) 2
      rwa [sq_abs] at h
    have hinv : 1 / ‖F.kmom k‖ ^ 2 ≤ (2 * E.KH * E.aScat) ^ 2 := by
      have h3 : 1 / ‖F.kmom k‖ ≤ 2 * E.KH * E.aScat := by
        have h5 := one_div_le_one_div_of_le
          (show (0 : ℝ) < 1 / (2 * E.KH * E.aScat) by positivity) (hPH k hk)
        rwa [one_div_one_div] at h5
      calc 1 / ‖F.kmom k‖ ^ 2 = (1 / ‖F.kmom k‖) ^ 2 := by rw [div_pow, one_pow]
        _ ≤ (2 * E.KH * E.aScat) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
    calc E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 = E.W1 k ^ 2 * (1 / ‖F.kmom k‖ ^ 2) := by ring
      _ ≤ (16 * Real.pi * E.aScat) ^ 2 * (2 * E.KH * E.aScat) ^ 2 :=
          mul_le_mul hW hinv (div_nonneg zero_le_one (sq_nonneg _)) (by positivity)
      _ = (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 := by ring
  have hmaxw0 : (0 : ℝ) ≤ (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 := by
    positivity
  have hns0 : 0 ≤ F.normSq f := by rw [FockData.normSq]; exact F.bp_nonneg f
  have hexc : ∀ s ∈ Work.BoseB7.excited L, s ≠ 0 :=
    fun s hs => (Finset.mem_erase.mp hs).1
  have hYsum' : (∑ p : L, F.bp (T.N (F.a p f)) (F.a p f)) ≤ 16 * M ^ 2 * F.normSq f :=
    le_trans (le_of_eq (Finset.sum_congr rfl fun p _ =>
      F.bp_symm (T.N (F.a p f)) (F.a p f))) hYsum
  -- ### 1. the shift representation and the `ccr` split of `‖Z_k†f‖²`
  have hZrepr : ∀ k : L, (shiftZDag F T E k) f
      = ∑ s ∈ Work.BoseB7.excited L, E.fL s • (F.aDag (s - k) (T.ta s f)) := by
    intro k
    rw [shiftZDag, sum_smul_apply_zp]
    simp only [LinearMap.comp_apply]
  have hsplit : ∀ k : L, F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)
      = (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
            E.fL s * E.fL s' * F.bp (F.a (s' - k) (T.ta s f)) (F.a (s - k) (T.ta s' f)))
        + (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
            E.fL s * E.fL s' * (F.ccrK (s - k) (s' - k) * F.bp (T.ta s f) (T.ta s' f))) := by
    intro k
    rw [hZrepr k, SumABound.bp_sum_sum]
    have hterm : ∀ s ∈ Work.BoseB7.excited L, ∀ s' ∈ Work.BoseB7.excited L,
        E.fL s * E.fL s' * F.bp (F.aDag (s - k) (T.ta s f)) (F.aDag (s' - k) (T.ta s' f))
          = E.fL s * E.fL s' * F.bp (F.a (s' - k) (T.ta s f)) (F.a (s - k) (T.ta s' f))
            + E.fL s * E.fL s' * (F.ccrK (s - k) (s' - k) * F.bp (T.ta s f) (T.ta s' f)) := by
      intro s _ s' _
      rw [bp_aDag_aDag F (s - k) (s' - k) (T.ta s f) (T.ta s' f)]
      ring
    rw [Finset.sum_congr rfl (fun s hs => Finset.sum_congr rfl (fun s' hs' => hterm s hs s' hs'))]
    simp only [Finset.sum_add_distrib]
  -- ### 2. the quadratic part, via AM–GM and the `ã`/`a` commutation
  have hAb : ∀ k : L,
      (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
          E.fL s * E.fL s' * F.bp (F.a (s' - k) (T.ta s f)) (F.a (s - k) (T.ta s' f)))
        ≤ ∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
            |E.fL s| * |E.fL s'| *
              F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f)) := by
    intro k
    have h1 := double_sum_amgm F (Work.BoseB7.excited L) E.fL
      (fun s s' => F.a (s' - k) (T.ta s f)) (fun s s' => F.a (s - k) (T.ta s' f))
      (fun s s' => rfl)
    refine le_trans h1 ?_
    refine Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun s' _ => ?_))
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact le_of_eq (bp_ta_a F T s (s' - k) f)
  -- ### 3. the commutator part, directly from `hccrB` (no `Cf`)
  have hBb : ∀ k : L,
      (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
          E.fL s * E.fL s' * (F.ccrK (s - k) (s' - k) * F.bp (T.ta s f) (T.ta s' f)))
        ≤ 100 * ∑ s ∈ Work.BoseB7.excited L, (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f) := by
    intro k
    refine le_trans (le_of_eq ?_) (hccrB k E.fL (fun s => T.ta s f))
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun s' _ => ?_))
    ring
  -- ### 4. the `k`-sum of the quadratic part
  have hA3 : (∑ s ∈ Work.BoseB7.excited L,
        ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f)))
      ≤ 16 * M ^ 2 * F.normSq f := by
    rw [Finset.sum_comm]
    calc ∑ p : L, ∑ s ∈ Work.BoseB7.excited L,
            F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f))
        ≤ ∑ p : L, F.bp (T.N (F.a p f)) (F.a p f) :=
          Finset.sum_le_sum (fun p _ => ta_sum_le F T _ hexc (F.a p f))
      _ ≤ 16 * M ^ 2 * F.normSq f := hYsum'
  have hAsum : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
        (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
            |E.fL s| * |E.fL s'| *
              F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f)))
      ≤ Cf * (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 *
          (16 * M ^ 2 * F.normSq f) := by
    -- (i) the weight `≤ maxw` is spent once, termwise
    have hstep1 : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
          (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
              |E.fL s| * |E.fL s'| *
                F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f)))
        ≤ (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 *
          ∑ k ∈ F.PHset E, (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
              |E.fL s| * |E.fL s'| *
                F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun k hk => ?_)
      exact mul_le_mul_of_nonneg_right (hwle k hk)
        (Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun s' _ =>
          mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (F.bp_nonneg _))
    -- (ii) reorganise `Σ_k Σ_s Σ_{s'}` into `Σ_s Σ_{s'} Σ_k`, then count with `k ↦ s'−k`
    have hstep2 : ∑ k ∈ F.PHset E, (∑ s ∈ Work.BoseB7.excited L,
            ∑ s' ∈ Work.BoseB7.excited L, |E.fL s| * |E.fL s'| *
              F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f)))
        ≤ Cf * ∑ s ∈ Work.BoseB7.excited L,
            ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f)) := by
      have hre : ∑ k ∈ F.PHset E, (∑ s ∈ Work.BoseB7.excited L,
              ∑ s' ∈ Work.BoseB7.excited L, |E.fL s| * |E.fL s'| *
                F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f)))
          = ∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
              ∑ k ∈ F.PHset E, |E.fL s| * |E.fL s'| *
                F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Finset.sum_comm]
      rw [hre]
      have hpull : ∀ s ∈ Work.BoseB7.excited L, ∀ s' ∈ Work.BoseB7.excited L,
          (∑ k ∈ F.PHset E, |E.fL s| * |E.fL s'| *
                F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f)))
            = |E.fL s| * |E.fL s'| * ∑ k ∈ F.PHset E,
                F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f)) := by
        intro s _ s' _
        rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun s hs => Finset.sum_congr rfl (fun s' hs' =>
        hpull s hs s' hs'))]
      have hshift : ∀ s ∈ Work.BoseB7.excited L, ∀ s' ∈ Work.BoseB7.excited L,
          |E.fL s| * |E.fL s'| *
              (∑ k ∈ F.PHset E, F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f)))
            ≤ |E.fL s| * |E.fL s'| *
              ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f)) := by
        intro s _ s' _
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        exact sum_shift_le (F.PHset E)
          (fun p => F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f)))
          (fun p => F.bp_nonneg _) s'
      refine le_trans (Finset.sum_le_sum (fun s hs => Finset.sum_le_sum (fun s' hs' =>
        hshift s hs s' hs'))) ?_
      -- the `s'`-sum only multiplies by `Σ_{s'}|f_L(s')| ≤ Cf`
      have hfac : (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
              |E.fL s| * |E.fL s'| *
                ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f)))
          = (∑ s ∈ Work.BoseB7.excited L,
              |E.fL s| * ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f))) *
            (∑ s' ∈ Work.BoseB7.excited L, |E.fL s'|) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s' _ => ?_)
        ring
      rw [hfac]
      have hZ0 : ∀ s : L, 0 ≤ ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f)) :=
        fun s => Finset.sum_nonneg fun p _ => F.bp_nonneg _
      have hcs0 : (0 : ℝ) ≤ ∑ s' ∈ Work.BoseB7.excited L, |E.fL s'| :=
        Finset.sum_nonneg fun s _ => abs_nonneg _
      have hfirst : (∑ s ∈ Work.BoseB7.excited L,
            |E.fL s| * ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f)))
          ≤ ∑ s ∈ Work.BoseB7.excited L,
              ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f)) := by
        refine Finset.sum_le_sum (fun s _ => ?_)
        have h1 : |E.fL s| ≤ 1 := hfl1 s
        have h2 : 0 ≤ ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f)) := hZ0 s
        nlinarith [h1, h2]
      calc (∑ s ∈ Work.BoseB7.excited L,
              |E.fL s| * ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f))) *
            (∑ s' ∈ Work.BoseB7.excited L, |E.fL s'|)
          ≤ (∑ s ∈ Work.BoseB7.excited L,
              ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f))) *
            (∑ s' ∈ Work.BoseB7.excited L, |E.fL s'|) :=
            mul_le_mul_of_nonneg_right hfirst hcs0
        _ ≤ (∑ s ∈ Work.BoseB7.excited L,
              ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f))) * Cf :=
            mul_le_mul_of_nonneg_left hcfs
              (Finset.sum_nonneg fun s _ => hZ0 s)
        _ = Cf * ∑ s ∈ Work.BoseB7.excited L,
              ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f)) := by ring
    calc ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
          (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
              |E.fL s| * |E.fL s'| *
                F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f)))
        ≤ (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 *
            ∑ k ∈ F.PHset E, (∑ s ∈ Work.BoseB7.excited L,
              ∑ s' ∈ Work.BoseB7.excited L, |E.fL s| * |E.fL s'| *
                F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f))) := hstep1
      _ ≤ (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 *
            (Cf * ∑ s ∈ Work.BoseB7.excited L,
              ∑ p : L, F.bp (T.ta s (F.a p f)) (T.ta s (F.a p f))) :=
          mul_le_mul_of_nonneg_left hstep2 hmaxw0
      _ ≤ (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 *
            (Cf * (16 * M ^ 2 * F.normSq f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA3 hCf) hmaxw0
      _ = Cf * (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 *
            (16 * M ^ 2 * F.normSq f) := by ring
  -- ### 5. the `k`-sum of the commutator part
  have hBsum : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
        (100 * ∑ s ∈ Work.BoseB7.excited L,
          (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f))
      ≤ 100 * Row * (M * F.normSq f) := by
    have hX : (∑ s ∈ Work.BoseB7.excited L,
          (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f)) ≤ M * F.normSq f := by
      refine le_trans (Finset.sum_le_sum (fun s _ => ?_)) hTasum
      have h1 : (E.fL s) ^ 2 ≤ 1 := by
        have h := hfl1 s
        rw [← sq_abs (E.fL s)]
        nlinarith [abs_nonneg (E.fL s)]
      simpa using mul_le_mul_of_nonneg_right h1 (F.bp_nonneg (T.ta s f))
    have hX0 : 0 ≤ ∑ s ∈ Work.BoseB7.excited L,
        (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f) :=
      Finset.sum_nonneg fun s _ => mul_nonneg (sq_nonneg _) (F.bp_nonneg _)
    have hrow0 : 0 ≤ ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => by positivity
    have hrew : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
          (100 * ∑ s ∈ Work.BoseB7.excited L,
            (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f))
        = 100 * ((∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) *
            (∑ s ∈ Work.BoseB7.excited L,
              (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f))) := by
      have h1 : ∀ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
            (100 * ∑ s ∈ Work.BoseB7.excited L,
              (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f))
          = 100 * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
              (∑ s ∈ Work.BoseB7.excited L,
                (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f))) := fun k _ => by ring
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [hrew]
    have h1 : (∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) *
          (∑ s ∈ Work.BoseB7.excited L,
            (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f)) ≤ Row * (M * F.normSq f) :=
      mul_le_mul hRowE hX hX0 hRow
    calc 100 * ((∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) *
          (∑ s ∈ Work.BoseB7.excited L, (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f)))
        ≤ 100 * (Row * (M * F.normSq f)) :=
          mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 100 by norm_num)
      _ = 100 * Row * (M * F.normSq f) := by ring
  -- ### 6. the wedge bound on `Σ_{k∈P_H} Ŵ₁(k)²/‖k‖² ‖Z_k†f‖²`
  have hwedgeW : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
        F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)
      ≤ (Cf * (2000 * (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * M ^ 2)
          + 2000 * Row * M) * F.normSq f := by
    have hperk : ∀ k ∈ F.PHset E,
        F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)
          ≤ (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
                |E.fL s| * |E.fL s'| *
                  F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f)))
            + 100 * (∑ s ∈ Work.BoseB7.excited L,
                (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f)) := by
      intro k _
      rw [hsplit k]
      exact add_le_add (hAb k) (hBb k)
    have hloose : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
          F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)
        ≤ (Cf * ((16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * (16 * M ^ 2))
            + 100 * Row * M) * F.normSq f := by
      have hframe : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
            F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)
          ≤ (∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
              (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
                |E.fL s| * |E.fL s'| *
                  F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f))))
            + (∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
              (100 * ∑ s ∈ Work.BoseB7.excited L,
                (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f))) := by
        calc ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
              F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)
            ≤ ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
                ((∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
                    |E.fL s| * |E.fL s'| *
                      F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f)))
                  + 100 * (∑ s ∈ Work.BoseB7.excited L,
                      (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f))) :=
              Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hperk k hk)
                (by positivity))
          _ = ∑ k ∈ F.PHset E, (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
                  (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
                    |E.fL s| * |E.fL s'| *
                      F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f)))
                + E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
                  (100 * (∑ s ∈ Work.BoseB7.excited L,
                      (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f)))) := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              ring
          _ = (∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
                (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
                  |E.fL s| * |E.fL s'| *
                    F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f))))
              + (∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
                (100 * (∑ s ∈ Work.BoseB7.excited L,
                    (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f)))) := by
              rw [Finset.sum_add_distrib]
      calc ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
            F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)
          ≤ (∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
              (∑ s ∈ Work.BoseB7.excited L, ∑ s' ∈ Work.BoseB7.excited L,
                |E.fL s| * |E.fL s'| *
                  F.bp (T.ta s (F.a (s' - k) f)) (T.ta s (F.a (s' - k) f))))
            + (∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 *
              (100 * ∑ s ∈ Work.BoseB7.excited L,
                (E.fL s) ^ 2 * F.bp (T.ta s f) (T.ta s f))) := hframe
        _ ≤ Cf * (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 *
              (16 * M ^ 2 * F.normSq f)
            + 100 * Row * (M * F.normSq f) := add_le_add hAsum hBsum
        _ = (Cf * ((16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * (16 * M ^ 2))
            + 100 * Row * M) * F.normSq f := by ring
    refine le_trans hloose ?_
    have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
    have hstep : (16 : ℝ) * M ^ 2 ≤ 2000 * M ^ 2 := by nlinarith [hM2]
    have hW16 : (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * (16 * M ^ 2)
        ≤ (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * (2000 * M ^ 2) :=
      mul_le_mul_of_nonneg_left hstep hmaxw0
    have hA16 : Cf * ((16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * (16 * M ^ 2))
        ≤ Cf * (2000 * (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * M ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hCf
      nlinarith [hW16]
    have hRM0 : 0 ≤ Row * M := mul_nonneg hRow hM
    have hB16 : 100 * Row * M ≤ 2000 * Row * M := by nlinarith [hRM0]
    have hb : Cf * ((16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * (16 * M ^ 2))
          + 100 * Row * M
        ≤ Cf * (2000 * (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * M ^ 2)
          + 2000 * Row * M := add_le_add hA16 hB16
    exact mul_le_mul_of_nonneg_right hb hns0
  -- ### 7. the wedge with the `ε`, `z`, `ℓ` factors restored
  have hwedge : ∑ k ∈ F.PHset E, (2 / (ε * ‖F.kmom k‖ ^ 2)) * ((E.z / E.ell ^ 3) * E.W1 k) ^ 2
          * F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)
      ≤ (2 / ε) * (E.z / E.ell ^ 3) ^ 2
          * (Cf * (2000 * (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * M ^ 2)
              + 2000 * Row * M) * F.normSq f := by
    have hfac : ∀ k ∈ F.PHset E,
        (2 / (ε * ‖F.kmom k‖ ^ 2)) * ((E.z / E.ell ^ 3) * E.W1 k) ^ 2
            * F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)
          = (2 / ε) * (E.z / E.ell ^ 3) ^ 2 * ((E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)
              * F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)) := by
      intro k hk
      have hk0 : ‖F.kmom k‖ ≠ 0 := ne_of_gt (hkp k hk)
      have he0 : ε ≠ 0 := ne_of_gt hε
      field_simp
      try ring
    calc ∑ k ∈ F.PHset E, (2 / (ε * ‖F.kmom k‖ ^ 2)) * ((E.z / E.ell ^ 3) * E.W1 k) ^ 2
            * F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)
        = (2 / ε) * (E.z / E.ell ^ 3) ^ 2
            * (∑ k ∈ F.PHset E, (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)
                * F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)) := by
          rw [Finset.sum_congr rfl (fun k hk => hfac k hk), Finset.mul_sum]
      _ ≤ (2 / ε) * (E.z / E.ell ^ 3) ^ 2
            * ((Cf * (2000 * (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * M ^ 2)
                + 2000 * Row * M) * F.normSq f) :=
          mul_le_mul_of_nonneg_left hwedgeW (by positivity)
      _ = (2 / ε) * (E.z / E.ell ^ 3) ^ 2
            * (Cf * (2000 * (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * M ^ 2)
                + 2000 * Row * M) * F.normSq f := by ring
  -- ### 8. the completing square, summed over `P_H`
  have hsq : -(∑ k ∈ F.PHset E, (2 / (ε * ‖F.kmom k‖ ^ 2)) * ((E.z / E.ell ^ 3) * E.W1 k) ^ 2
          * F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f))
      ≤ F.qw f (T.Q3T E)
        + ∑ k ∈ F.PHset E, (ε * ‖F.kmom k‖ ^ 2 / 2) * F.bp (F.a k f) (F.a k f) := by
    have hperk : ∀ k ∈ F.PHset E,
        -((2 / (ε * ‖F.kmom k‖ ^ 2)) * ((E.z / E.ell ^ 3) * E.W1 k) ^ 2
            * F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f))
          ≤ (ε * ‖F.kmom k‖ ^ 2 / 2) * F.bp (F.a k f) (F.a k f)
            + 2 * ((E.z / E.ell ^ 3) * E.W1 k)
                * F.bp (F.a k f) ((shiftZDag F T E k) f) := by
      intro k hk
      rw [show -((2 / (ε * ‖F.kmom k‖ ^ 2)) * ((E.z / E.ell ^ 3) * E.W1 k) ^ 2
            * F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f))
          = -(2 / (ε * ‖F.kmom k‖ ^ 2)) * ((E.z / E.ell ^ 3) * E.W1 k) ^ 2
            * F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f) from by ring]
      exact Q3T_block_ge F T E hε (hkp k hk) f
    have hBs : ∑ k ∈ F.PHset E, 2 * ((E.z / E.ell ^ 3) * E.W1 k)
          * F.bp (F.a k f) ((shiftZDag F T E k) f) = F.qw f (T.Q3T E) := by
      rw [qw_Q3T_eq F T E f, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [← Finset.sum_neg_distrib]
    refine le_trans (Finset.sum_le_sum hperk) ?_
    rw [Finset.sum_add_distrib, hBs]
    exact le_of_eq (add_comm _ _)
  -- ### 9. the kinetic reserve dominates the kinetic blocks
  have hK : F.qw f (∑ k : L, (ε * E.tau k) • F.nOp k)
      = ∑ k : L, ε * E.tau k * F.bp (F.a k f) (F.a k f) := by
    rw [qw_sum_finset_zp]
    exact Finset.sum_congr rfl fun k _ => by rw [qw_nOp_self]
  have hresEq : 1 / 2 * ∑ k : L, ε * E.tau k * F.qw f (F.nOp k + F.nOp (-k))
      = ∑ k : L, ε * E.tau k * F.bp (F.a k f) (F.a k f) := by
    have hre : (∑ k : L, ε * E.tau k * F.bp (F.a (-k) f) (F.a (-k) f))
        = ∑ k : L, ε * E.tau k * F.bp (F.a k f) (F.a k f) := by
      refine Fintype.sum_equiv (Equiv.neg L) _ _ (fun k => by simp [Equiv.neg_apply, hτeven])
    have h1 : ∀ k : L, ε * E.tau k * F.qw f (F.nOp k + F.nOp (-k))
        = ε * E.tau k * F.bp (F.a k f) (F.a k f)
          + ε * E.tau k * F.bp (F.a (-k) f) (F.a (-k) f) := by
      intro k
      rw [qw_nOp_add]
      ring
    rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_add_distrib, hre]
    ring
  have hres : ∑ k ∈ F.PHset E, (ε * ‖F.kmom k‖ ^ 2 / 2) * F.bp (F.a k f) (F.a k f)
      ≤ F.qw f (∑ k : L, (ε * E.tau k) • F.nOp k) := by
    calc ∑ k ∈ F.PHset E, (ε * ‖F.kmom k‖ ^ 2 / 2) * F.bp (F.a k f) (F.a k f)
        ≤ 1 / 2 * ∑ k : L, ε * E.tau k * F.qw f (F.nOp k + F.nOp (-k)) :=
          reserve_ge F E (le_of_lt hε) hτ0 hτeven hτge f
      _ = ∑ k : L, ε * E.tau k * F.bp (F.a k f) (F.a k f) := hresEq
      _ = F.qw f (∑ k : L, (ε * E.tau k) • F.nOp k) := hK.symm
  -- ### 10. assembly
  have h1 : -((2 / ε) * (E.z / E.ell ^ 3) ^ 2
        * (Cf * (2000 * (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * M ^ 2)
            + 2000 * Row * M) * F.normSq f)
      ≤ -(∑ k ∈ F.PHset E, (2 / (ε * ‖F.kmom k‖ ^ 2)) * ((E.z / E.ell ^ 3) * E.W1 k) ^ 2
          * F.bp ((shiftZDag F T E k) f) ((shiftZDag F T E k) f)) :=
    neg_le_neg hwedge
  rw [show -(2 / ε) * (E.z / E.ell ^ 3) ^ 2
        * (Cf * (2000 * (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * M ^ 2)
            + 2000 * Row * M) * F.normSq f
      = -((2 / ε) * (E.z / E.ell ^ 3) ^ 2
        * (Cf * (2000 * (16 * Real.pi * E.aScat * (2 * E.KH * E.aScat)) ^ 2 * M ^ 2)
            + 2000 * Row * M) * F.normSq f) from by ring]
  linarith [h1, hsq, hres]

end Work.BoseFixR
