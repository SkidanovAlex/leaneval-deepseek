import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongLWP.Sobolev.holder_half_of_W22
import Submission.Work.FTS.StrongLWP.Sobolev.Prelim
import Submission.Work.FTS.StrongLWP.Sobolev.EqcBasis
import Submission.Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2
import Submission.Work.FTS.StrongEps.LocUnif.LocAux
import Submission.Work.FTS.StrongEps.LocUnif.LocTower
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false
set_option maxHeartbeats 1000000


/-! ## The seven rectangle integrals and the extraction inputs -/

/-- **The seven rectangle integrals** of a mixed family `mixed j i F` and of its first two partial
derivatives, all bounded by `C · HkSq α 6 F`. -/
def Rect7 (α : ℝ) (F : ℝ → ℝ → ℝ) (j i : ℕ) (a b c d C : ℝ) : Prop :=
  (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
      (Work.Spaces.mixed j i F z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
  (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
  (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
  (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 F) ∧
  (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 F) ∧
  (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 F) ∧
  (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ C * Work.Spaces.HkSq α 6 F)

/-- The fifteen pairs `(j,i)` with `j + i ≤ 4`. -/
def pairs : Fin 15 → ℕ × ℕ :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1),
    (2, 2), (3, 0), (3, 1), (4, 0)]

theorem pairs_mem : ∀ m : Fin 15, (pairs m).1 + (pairs m).2 ≤ 4 := by
  intro m; fin_cases m <;> decide

theorem pairs_surj (c d : ℕ) (h : c + d ≤ 4) : ∃ m : Fin 15, pairs m = (c, d) := by
  have hc : c ≤ 4 := by omega
  have hd : d ≤ 4 := by omega
  interval_cases c <;> interval_cases d <;> first | (exfalso; omega) | decide

/-- The index of a pair `(c,d)` with `c + d ≤ 4` in the list `pairs`. -/
noncomputable def idx (c d : ℕ) : Fin 15 :=
  if h : c + d ≤ 4 then Classical.choose (pairs_surj c d h) else 0

theorem idx_spec {c d : ℕ} (h : c + d ≤ 4) : pairs (idx c d) = (c, d) := by
  rw [idx, dif_pos h]
  exact Classical.choose_spec (pairs_surj c d h)

/-- The vector family of the fifteen mixed derivatives. -/
def fam (G : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : Fin 15 → ℝ :=
  fun m => Work.Spaces.mixed (pairs m).1 (pairs m).2 (G n) p.1 p.2

/-- A bound for the sup-norm of a `Fin k`-valued function by the sum of the absolute values. -/
theorem norm_fin_le_sum (k : ℕ) (f : Fin k → ℝ) : ‖f‖ ≤ ∑ m : Fin k, |f m| := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun m _ => abs_nonneg _)).mpr fun m => ?_
  calc ‖f m‖ = |f m| := Real.norm_eq_abs _
    _ ≤ ∑ m' : Fin k, |f m'| :=
        Finset.single_le_sum (f := fun m' => |f m'|) (fun m' _ => abs_nonneg _)
          (Finset.mem_univ m)

/-- The components of a locally uniformly convergent family into `Fin k → ℝ` converge locally
uniformly. -/
theorem tendstoLocallyUniformlyOn_Q0_apply {k : ℕ} {F : ℕ → ℝ × ℝ → (Fin k → ℝ)}
    {g : ℝ × ℝ → (Fin k → ℝ)} {m : Fin k}
    (h : TendstoLocallyUniformlyOn F g Filter.atTop Work.FTS.EllipticEst.Q0) :
    TendstoLocallyUniformlyOn (fun n p => F n p m) (fun p => g p m) Filter.atTop
      Work.FTS.EllipticEst.Q0 := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Work.FTS.EllipticEst.isOpen_Q0] at h ⊢
  intro K hKQ hK
  have h1 := Metric.tendstoUniformlyOn_iff.mp (h K hKQ hK)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h1 ε hε] with n hn p hp
  exact lt_of_le_of_lt (dist_le_pi_dist (g p) (F n p) m) (hn p hp)

/-! ## The extraction inputs as a structure -/

/-- **The three analytic inputs of the extraction**, packaged so that they can be supplied by the
sibling files (`mixed_rect_L2_bounds`, `mixed_morrey_step`,
`exists_subseq_tendstoLocallyUniformlyOn_fin`) once they are proved. -/
structure Inputs (α : ℝ) : Prop where
  /-- the seven rectangle `L²`-bounds for the mixed families and their first two derivatives. -/
  L2 : ∀ {a b c d : ℝ}, 0 < a → a ≤ b → 0 < c → d < π / 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen F →
      Work.Spaces.HkMem α 6 F → ∀ (j i : ℕ), j + i ≤ 4 → Rect7 α F j i a b c d C
  /-- the Morrey (Hölder-`1/2`) step for the mixed families. -/
  Mor : ∀ {χ : ℝ × ℝ → ℝ} {F : ℝ → ℝ → ℝ} {C C₀ M Km : ℝ}
      {a b c d a' b' c' d' : ℝ},
      (∀ (v : ℝ × ℝ → ℝ), ContDiff ℝ 2 v → HasCompactSupport v →
        ∀ p q : ℝ × ℝ, |v p - v q| ≤ Km * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
          + Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) * dist p q ^ (1 / 2 : ℝ)) →
      0 ≤ Km → 0 < α → 0 ≤ C₀ → 0 < C → ContDiff ℝ 2 χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x) → (∀ x, χ x ≤ 1) →
      (∀ z, z ∈ Set.Icc a b → ∀ θ, θ ∈ Set.Icc c d → χ (z, θ) = 1) →
      (∀ x, x ∉ Set.Icc a' b' ×ˢ Set.Icc c' d' → χ x = 0) →
      (∀ x, ‖fderiv ℝ χ x‖ ≤ M) → (∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ M) →
      Set.Icc a' b' ×ˢ Set.Icc c' d' ⊆ Work.FTS.EllipticEst.Q0 →
      Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α 6 F →
      Work.Spaces.HkNorm α 6 F ≤ C₀ →
      (∀ (j i : ℕ), j + i ≤ 4 → Rect7 α F j i a' b' c' d' C) →
      ∀ (j i : ℕ), j + i ≤ 4 → ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d,
        ∀ q ∈ Set.Icc a b ×ˢ Set.Icc c d,
          |Work.Spaces.mixed j i F p.1 p.2 - Work.Spaces.mixed j i F q.1 q.2|
            ≤ (Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * C₀))
              * dist p q ^ (1 / 2 : ℝ)
  /-- the sup-bound from a Hölder-`1/2` bound and an `L²`-bound on a nondegenerate rectangle. -/
  Sup : ∀ (M : ℕ → ℝ → ℝ → ℝ) {a b c d C₁ C₂ : ℝ},
      a < b → c < d → 0 ≤ C₁ → 0 ≤ C₂ →
      (∀ n : ℕ, ContinuousOn (fun p : ℝ × ℝ => M n p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d)) →
      (∀ n p q, p ∈ Set.Icc a b ×ˢ Set.Icc c d → q ∈ Set.Icc a b ×ˢ Set.Icc c d →
        |M n p.1 p.2 - M n q.1 q.2| ≤ C₁ * dist p q ^ (1 / 2 : ℝ)) →
      (∀ n, ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (M n z θ) ^ 2 ≤ C₂) →
      ∃ C : ℝ, 0 < C ∧ ∀ n p, p ∈ Set.Icc a b ×ˢ Set.Icc c d → |M n p.1 p.2| ≤ C
  /-- the Arzelà–Ascoli extraction for a finite family of vector-valued functions. -/
  Ext : ∀ {k : ℕ} {U : Set (ℝ × ℝ)}, IsOpen U → ∀ {F : ℕ → ℝ × ℝ → (Fin k → ℝ)},
      (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ n : ℕ, ∀ p ∈ K, ‖F n p‖ ≤ C) →
      (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ U → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K, dist p q < δ → ‖F n p - F n q‖ < ε) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℝ × ℝ → (Fin k → ℝ),
        TendstoLocallyUniformlyOn (fun n p => F (φ n) p) f Filter.atTop U

/-- From a compact `K ⊆ Q0` we produce a nondegenerate rectangle `[a,b] × [c,d]` containing `K`
and a strictly larger rectangle `[a',b'] × [c',d'] ⊆ Q0` containing it, with the strict inclusions
required by the cutoff construction (`a' < a ≤ b < b'`, `c' < c ≤ d < d'`). -/
theorem exists_rects (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ a b c d a' b' c' d' : ℝ,
      0 < a' ∧ a' < a ∧ a ≤ b ∧ b < b' ∧ 0 < c' ∧ c' < c ∧ c ≤ d ∧ d < d' ∧ d' < π / 2 ∧
      K ⊆ Set.Icc a b ×ˢ Set.Icc c d ∧
      Set.Icc a b ×ˢ Set.Icc c d ⊆ Set.Icc a' b' ×ˢ Set.Icc c' d' ∧
      a < b ∧ c < d := by
  obtain ⟨A, B, C, D, hA, hAB, hC, hCD, hD, hKsub⟩ :=
    Work.FTS.StrongLWP.exists_rect_of_compact_subset_Q0 hK hKQ
  refine ⟨3 * A / 4, B + 1, 3 * C / 4, (D + π / 2) / 2, A / 2, B + 2, C / 2,
    ((D + π / 2) / 2 + π / 2) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try (linarith [Real.pi_pos])
  · intro p hp
    exact ⟨⟨by linarith [(hKsub hp).1.1], by linarith [(hKsub hp).1.2]⟩,
      ⟨by linarith [(hKsub hp).2.1], by linarith [(hKsub hp).2.2]⟩⟩
  · intro p hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, ⟨by linarith [hp.2.1],
      by linarith [hp.2.2]⟩⟩

/-- **The uniform bounds for the fifteen mixed families on a compact subset of `Q0`.**  For every
compact `K ⊆ Q0` and every pair `(j,i)` with `j + i ≤ 4` there are constants `C₁, C₂ > 0` such
that all the families `mixed j i (G n)` are `C₁`-Hölder-`1/2` and bounded by `C₂` on `K`,
uniformly in `n`. -/
theorem family_bounds_on_compact {α B : ℝ} (hα : 0 < α) {G : ℕ → ℝ → ℝ → ℝ}
    (hI : Inputs α)
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (j i : ℕ) (hji : j + i ≤ 4) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      (∀ n p q, p ∈ K → q ∈ K →
        |Work.Spaces.mixed j i (G n) p.1 p.2 - Work.Spaces.mixed j i (G n) q.1 q.2|
          ≤ C₁ * dist p q ^ (1 / 2 : ℝ)) ∧
      (∀ n p, p ∈ K → |Work.Spaces.mixed j i (G n) p.1 p.2| ≤ C₂) := by
  have hB : 0 ≤ B := (Work.Spaces.HkNorm_nonneg α 6 (G 0)).trans (hb 0)
  obtain ⟨Km, hKmpos, hmor⟩ := Work.FTS.StrongLWP.Sobolev.holder_half_of_W22_real
  obtain ⟨a, b, c, d, a', b', c', d', ha'pos, ha'a, hab, hbb', hc'pos, hc'c, hcd, hdd', hd'pi,
    hKsub, hsub, hab', hcd'⟩ := exists_rects K hK hKQ
  obtain ⟨C, hCpos, hCL2⟩ := hI.L2 ha'pos (le_of_lt (lt_trans (lt_of_lt_of_le ha'a hab) hbb'))
    hc'pos hd'pi
  obtain ⟨χ, M, hMpos, hχC2, hχcs, hχnn, hχle1, hχone, hχzero, hMfd1, hMfd2⟩ :=
    Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2 ha'pos ha'a hab hbb' hc'pos hc'c hcd
      hdd' hd'pi
  have hsubQ : Set.Icc a' b' ×ˢ Set.Icc c' d' ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
    obtain ⟨hp1a, hp1b⟩ := Set.mem_Icc.mp hp1
    obtain ⟨hp2a, hp2b⟩ := Set.mem_Icc.mp hp2
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨by linarith, by linarith [Real.pi_pos], by linarith⟩
  -- the Morrey (Hölder) bound on the inner rectangle
  have hholder : ∀ n : ℕ, ∀ p q : ℝ × ℝ, p ∈ Set.Icc a b ×ˢ Set.Icc c d →
      q ∈ Set.Icc a b ×ˢ Set.Icc c d →
      |Work.Spaces.mixed j i (G n) p.1 p.2 - Work.Spaces.mixed j i (G n) q.1 q.2|
        ≤ (Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * B))
          * dist p q ^ (1 / 2 : ℝ) :=
    fun n p q hp hq => hI.Mor hmor hKmpos.le hα hB hCpos (hχC2 2) hχcs hχnn hχle1 hχone hχzero
      hMfd1 hMfd2 hsubQ (hsm n) (hmem n) (hb n)
      (fun j' i' hji' => hCL2 (G n) (hsm n) (hmem n) j' i' hji') j i hji p hp q hq
  -- the `L²`-bound on the inner rectangle
  have hL2inner : ∀ n : ℕ,
      ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.mixed j i (G n) z θ) ^ 2
        ≤ C * B ^ 2 := by
    intro n
    have hHk : Work.Spaces.HkSq α 6 (G n) ≤ B ^ 2 := by
      have h1 : Work.Spaces.HkSq α 6 (G n) = (Real.sqrt (Work.Spaces.HkSq α 6 (G n))) ^ 2 :=
        (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 (G n))).symm
      rw [h1]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hb n) 2
    have hcontR : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.mixed j i (G n) p.1 p.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      ((((hsm n).mixed j i).continuousOn).mono hsubQ).pow 2
    have hint : IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.mixed j i (G n) p.1 p.2) ^ 2)
        (Set.Icc a' b' ×ˢ Set.Icc c' d') :=
      hcontR.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hmono : (∫ p in Set.Icc a b ×ˢ Set.Icc c d,
          (Work.Spaces.mixed j i (G n) p.1 p.2) ^ 2)
        ≤ ∫ p in Set.Icc a' b' ×ˢ Set.Icc c' d',
            (Work.Spaces.mixed j i (G n) p.1 p.2) ^ 2 :=
      setIntegral_mono_set hint (Eventually.of_forall fun p => sq_nonneg _)
        (Eventually.of_forall fun p hp => hsub hp)
    rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq hint] at hmono
    rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq
      ((hint.mono_set hsub))] at hmono
    refine hmono.trans ?_
    exact (hCL2 (G n) (hsm n) (hmem n) j i hji).1.trans (mul_le_mul_of_nonneg_left hHk hCpos.le)
  -- the sup bound on the inner rectangle
  have hsubInner : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
    obtain ⟨hp1a, hp1b⟩ := Set.mem_Icc.mp hp1
    obtain ⟨hp2a, hp2b⟩ := Set.mem_Icc.mp hp2
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨by linarith [ha'pos, ha'a], by linarith [hc'pos, hc'c, Real.pi_pos],
        by linarith [hdd', hd'pi]⟩
  have hC₁nn : 0 ≤ Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * B) :=
    mul_nonneg hKmpos.le (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hB)
  have hC₂nn : 0 ≤ C * B ^ 2 := mul_nonneg hCpos.le (by positivity)
  obtain ⟨C₂, hC₂pos, hC₂⟩ := hI.Sup (fun n z θ => Work.Spaces.mixed j i (G n) z θ)
    hab' hcd' hC₁nn hC₂nn
    (fun n => (((hsm n).mixed j i).continuousOn).mono hsubInner)
    hholder hL2inner
  refine ⟨Km * (2 * Real.sqrt (C + 3 * C * (16 + 17 * M ^ 2)) * B) + 1, C₂, by positivity, hC₂pos,
    ?_, ?_⟩
  · intro n p q hp hq
    exact (hholder n p q (hKsub hp) (hKsub hq)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (Real.rpow_nonneg dist_nonneg _))
  · intro n p hp
    exact hC₂ n p (hKsub hp)

/-- **The extraction and the tower relations, conditional on the three analytic inputs** (the
`L²`-bounds `mixed_rect_L2_bounds`, the Morrey step `mixed_morrey_step` and the extraction
`exists_subseq_tendstoLocallyUniformlyOn_fin`, together with the sup-bound
`sup_bound_of_holder_L2`). -/
theorem exists_limData {α B : ℝ} (hα : 0 < α)
    {G : ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hI : Inputs α) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℕ → ℕ → ℝ → ℝ → ℝ,
      LimData G φ F := by
  classical
  -- the uniform bounds on every compact, for each of the fifteen families
  have hfam : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∀ m : Fin 15,
      ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
        (∀ n p q, p ∈ K → q ∈ K →
          |Work.Spaces.mixed (pairs m).1 (pairs m).2 (G n) p.1 p.2
            - Work.Spaces.mixed (pairs m).1 (pairs m).2 (G n) q.1 q.2|
            ≤ C₁ * dist p q ^ (1 / 2 : ℝ)) ∧
        (∀ n p, p ∈ K → |Work.Spaces.mixed (pairs m).1 (pairs m).2 (G n) p.1 p.2| ≤ C₂) :=
    fun K hK hKQ m => family_bounds_on_compact hα hI hsm hmem hb K hK hKQ (pairs m).1 (pairs m).2
      (pairs_mem m)
  -- the two hypotheses of the extraction
  have hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ n : ℕ, ∀ p ∈ K, ‖fam G n p‖ ≤ C := by
    intro K hK hKQ
    choose C₁ C₂ hC₁pos hC₂pos hC₁ hC₂ using hfam K hK hKQ
    refine ⟨∑ m : Fin 15, C₂ m, ?_⟩
    intro n p hp
    calc ‖fam G n p‖ ≤ ∑ m : Fin 15, |fam G n p m| := norm_fin_le_sum _ _
      _ ≤ ∑ m : Fin 15, C₂ m := Finset.sum_le_sum fun m _ => hC₂ m n p hp
  have heqc : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K, dist p q < δ →
        ‖fam G n p - fam G n q‖ < ε := by
    intro K hK hKQ ε hε
    choose C₁ C₂ hC₁pos hC₂pos hC₁ hC₂ using hfam K hK hKQ
    have hSpos : 0 < (∑ m : Fin 15, C₁ m) + 1 := by
      refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun m _ => (hC₁pos m).le) one_pos
    refine ⟨(ε / ((∑ m : Fin 15, C₁ m) + 1)) ^ (2 : ℝ), ?_, fun n p hp q hq hpq => ?_⟩
    · exact Real.rpow_pos_of_pos (by positivity) _
    · have hstep : ‖fam G n p - fam G n q‖ ≤ (∑ m : Fin 15, C₁ m) * dist p q ^ (1 / 2 : ℝ) := by
        calc ‖fam G n p - fam G n q‖ ≤ ∑ m : Fin 15, |fam G n p m - fam G n q m| :=
              norm_fin_le_sum _ _
          _ ≤ ∑ m : Fin 15, C₁ m * dist p q ^ (1 / 2 : ℝ) :=
              Finset.sum_le_sum fun m _ => hC₁ m n p q hp hq
          _ = (∑ m : Fin 15, C₁ m) * dist p q ^ (1 / 2 : ℝ) := by rw [Finset.sum_mul]
      refine lt_of_le_of_lt hstep ?_
      have hδ : dist p q ^ (1 / 2 : ℝ) < ε / ((∑ m : Fin 15, C₁ m) + 1) := by
        have h2 : ((ε / ((∑ m : Fin 15, C₁ m) + 1)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
            = ε / ((∑ m : Fin 15, C₁ m) + 1) := by
          rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ε / ((∑ m : Fin 15, C₁ m) + 1))]
          norm_num
        rw [← h2]
        exact Real.rpow_lt_rpow dist_nonneg hpq (by norm_num)
      have h2 : (∑ m : Fin 15, C₁ m) * dist p q ^ (1 / 2 : ℝ)
          < ((∑ m : Fin 15, C₁ m) + 1) * (ε / ((∑ m : Fin 15, C₁ m) + 1)) := by
        have hsum_nonneg : 0 ≤ ∑ m : Fin 15, C₁ m := Finset.sum_nonneg fun m _ => (hC₁pos m).le
        calc (∑ m : Fin 15, C₁ m) * dist p q ^ (1 / 2 : ℝ)
            ≤ ((∑ m : Fin 15, C₁ m) + 1) * dist p q ^ (1 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
                (Real.rpow_nonneg dist_nonneg _)
          _ < ((∑ m : Fin 15, C₁ m) + 1) * (ε / ((∑ m : Fin 15, C₁ m) + 1)) :=
              mul_lt_mul_of_pos_left hδ hSpos
      rwa [mul_div_cancel₀ ε (ne_of_gt hSpos)] at h2
  obtain ⟨φ, hφ, glim, hgl : TendstoLocallyUniformlyOn (fun n p => fam G (φ n) p) glim
      Filter.atTop Work.FTS.EllipticEst.Q0⟩ := hI.Ext Work.FTS.EllipticEst.isOpen_Q0 hbdd heqc
  -- the limit families
  refine ⟨φ, hφ, fun c d => fun z θ => glim (z, θ) (idx c d), ?_⟩
  refine limData_of_conv hsm ?_
  intro c d hcd
  have happly := tendstoLocallyUniformlyOn_Q0_apply (m := idx c d) hgl
  have hfun : (fun (n : ℕ) (p : ℝ × ℝ) => fam G (φ n) p (idx c d))
      = fun n p => Work.Spaces.mixed c d (G (φ n)) p.1 p.2 := by
    funext n p
    simp only [fam]
    rw [idx_spec hcd]
  rwa [hfun] at happly


/-- **The three clauses of the conclusion, from `LimData`.** -/
theorem conclusion_of_limData {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n)) (h : LimData G φ F) :
    (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
        TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G (φ n) p.1 p.2)
          (fun p => F 0 0 p.1 p.2) Filter.atTop K) ∧
      ContDiffOn ℝ 4 (Function.uncurry (F 0 0)) Work.FTS.EllipticEst.Q0 ∧
      ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K →
        K ⊆ Work.FTS.EllipticEst.Q0 →
        TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (φ n)) p.1 p.2)
          (fun p => Work.Spaces.mixed j i (F 0 0) p.1 p.2) Filter.atTop K := by
  refine ⟨?_, contDiffOn_four_of_LimData hsm h, ?_⟩
  · intro K hK hKQ
    exact (tendstoLocallyUniformlyOn_iff_forall_isCompact
      Work.FTS.EllipticEst.isOpen_Q0).mp (h.conv 0 0 (by norm_num)) K hKQ hK
  · intro j i hji K hK hKQ
    have h1 : TendstoLocallyUniformlyOn
        (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (φ n)) p.1 p.2)
        (fun p => Work.Spaces.mixed j i (F 0 0) p.1 p.2) Filter.atTop
        Work.FTS.EllipticEst.Q0 :=
      (h.conv j i hji).congr_right (identify h j i hji)
    exact (tendstoLocallyUniformlyOn_iff_forall_isCompact
      Work.FTS.EllipticEst.isOpen_Q0).mp h1 K hKQ hK

end Work.FTS.StrongEps.LocUnif
