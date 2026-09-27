import Mathlib
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.UmlaufSetup
import Submission.Work.Drive.DirCTools
import Submission.Work.Drive.curve_deriv_ne_zero
import Submission.Work.Drive.secant_dirC_limit

namespace Work.Drive

open Manifold Topology Filter
open scoped Manifold ContDiff
open Submission.Collision (dirC)
open Submission.Configuration
open Submission.Geometry (eucNorm eucNorm_pos eucNorm_eq_zero)

/-! # `GoodC γ` is closed, i.e. `Zc γ` is open

`GoodC γ = {u | ∃ two chords of `γ` with equal midpoint, equal length and doubled directions
differing by `u`}`, and we show that it is closed *for any continuous injective `γ`*.

The point is that the `Sset`-decomposition of `GoodC γ`
(`Submission.Configuration.goodC_eq_iUnion`: `GoodC γ = ⋃ n, fst '' Sset γ n`) is an *increasing*
union of compact sets, so it gives no immediate information; but if `u k → u` with `u k ∈ GoodC γ`,
one passes to a convergent subsequence of the witnessing configurations.  In the limit, either the
first chord is nondegenerate — and then the midpoint/length/direction equations pass to the limit by
continuity (of `midPair`, `lenPair`, and of `dirPair` away from the diagonal), so that the limit
configuration is a witness for `u`; or the first chord is degenerate, in which case equal lengths force
the second chord to be degenerate too, all four points coincide at `γ z`, and both chords have
directions tending to the doubled direction of the tangent at `z`
(`chord_dirC_limit`), so that `u = 0`, which is always a collision angle
(`zero_mem_GoodC`: compare a chord with the reversed chord). -/

/-- The plane curve `t ↦ γ (Circle.exp t)` of a smooth embedded closed plane curve is `C¹`. -/
lemma contDiff_curve (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ∞ γ) : ContDiff ℝ 1 (curve γ) := by
  have hn1 : (1 : ℕ∞ω) ≤ ∞ := by simp
  have h1 : ContMDiff (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) 1 γ := hγ.contMDiff.of_le hn1
  have h2 : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ)) 1 (curve γ) :=
    h1.comp (contMDiff_circleExp (m := 1))
  exact contMDiff_iff_contDiff.mp h2

/-- **Short chords of a smooth embedded plane curve have directions tending to the tangent.**

If `x n ≠ y n` are points of the circle tending to `z = Circle.exp t₀`, then the doubled direction of
the chord from `γ (x n)` to `γ (y n)` tends to the doubled direction of the tangent
`deriv (curve γ) t₀`.

Proof: `Circle.exp` is a local homeomorphism (`isLocalHomeomorph_circleExp`); let `e` be a local
inverse of it at `t₀`.  Lifting the points `x n`, `y n` through `e` (and through an arbitrary lift
where `e` is not defined) gives sequences `s n`, `t n` with `Circle.exp (s n) = x n`,
`Circle.exp (t n) = y n`, `s n ≠ t n` and `s n, t n → t₀`, so the one-dimensional secant lemma
`Work.Drive.secant_dirC_limit` applies to `curve γ`. -/
lemma chord_dirC_limit (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ∞ γ) {t₀ : ℝ} {z : Circle}
    (hz : Circle.exp t₀ = z) {x y : ℕ → Circle}
    (hx : Tendsto x atTop (𝓝 z)) (hy : Tendsto y atTop (𝓝 z)) (hxy : ∀ n, x n ≠ y n) :
    Tendsto (fun n => dirC (γ (x n) - γ (y n))) atTop (𝓝 (dirC (deriv (curve γ) t₀))) := by
  classical
  have hG : ContDiff ℝ 1 (curve γ) := contDiff_curve γ hγ
  have hne : deriv (curve γ) t₀ ≠ 0 := curve_deriv_ne_zero γ hγ t₀
  -- a local inverse of `Circle.exp` at `t₀`
  let e : OpenPartialHomeomorph Circle ℝ :=
    IsLocalHomeomorph.localInverseAt isLocalHomeomorph_circleExp t₀
  have hzsrc : z ∈ e.source := by
    have h := IsLocalHomeomorph.apply_self_mem_localInverseAt_source
      (f := (Circle.exp : ℝ → Circle)) isLocalHomeomorph_circleExp (x := t₀)
    rwa [hz] at h
  have hez : e z = t₀ := by
    have h := IsLocalHomeomorph.localInverseAt_apply_self
      (f := (Circle.exp : ℝ → Circle)) isLocalHomeomorph_circleExp (x := t₀)
    rwa [hz] at h
  -- lifts of the two sequences
  let s : ℕ → ℝ := fun n => if h : x n ∈ e.source then e (x n)
      else Classical.choose (Circle.exp_surjective (x n))
  let t : ℕ → ℝ := fun n => if h : y n ∈ e.source then e (y n)
      else Classical.choose (Circle.exp_surjective (y n))
  have hsexp : ∀ n, Circle.exp (s n) = x n := by
    intro n
    by_cases h : x n ∈ e.source
    · show Circle.exp (if h : x n ∈ e.source then e (x n)
          else _) = x n
      rw [dif_pos h]
      exact IsLocalHomeomorph.apply_localInverseAt_of_mem
        (f := (Circle.exp : ℝ → Circle)) isLocalHomeomorph_circleExp h
    · show Circle.exp (if h : x n ∈ e.source then e (x n)
          else _) = x n
      rw [dif_neg h]
      exact Classical.choose_spec (Circle.exp_surjective (x n))
  have htexp : ∀ n, Circle.exp (t n) = y n := by
    intro n
    by_cases h : y n ∈ e.source
    · show Circle.exp (if h : y n ∈ e.source then e (y n)
          else _) = y n
      rw [dif_pos h]
      exact IsLocalHomeomorph.apply_localInverseAt_of_mem
        (f := (Circle.exp : ℝ → Circle)) isLocalHomeomorph_circleExp h
    · show Circle.exp (if h : y n ∈ e.source then e (y n)
          else _) = y n
      rw [dif_neg h]
      exact Classical.choose_spec (Circle.exp_surjective (y n))
  have hst : ∀ n, s n ≠ t n := by
    intro n h
    exact hxy n (by rw [← hsexp n, ← htexp n, h])
  -- convergence of the lifts
  have hxev : ∀ᶠ n in atTop, x n ∈ e.source :=
    hx.eventually (e.open_source.mem_nhds hzsrc)
  have hyev : ∀ᶠ n in atTop, y n ∈ e.source :=
    hy.eventually (e.open_source.mem_nhds hzsrc)
  have hslim : Tendsto s atTop (𝓝 t₀) := by
    have hcont : ContinuousWithinAt (fun a : Circle => e a) e.source z :=
      e.continuousOn.continuousWithinAt hzsrc
    have hwithin : Tendsto x atTop (𝓝[e.source] z) :=
      tendsto_nhdsWithin_iff.mpr ⟨hx, hxev⟩
    have hlim : Tendsto (fun n => e (x n)) atTop (𝓝 t₀) := by
      have h' : Tendsto (fun n => e (x n)) atTop (𝓝 (e z)) :=
        Filter.Tendsto.comp hcont hwithin
      rw [hez] at h'
      exact h'
    refine hlim.congr' ?_
    filter_upwards [hxev] with n hn
    show e (x n) = if h : x n ∈ e.source then e (x n) else _
    rw [dif_pos hn]
  have htlim : Tendsto t atTop (𝓝 t₀) := by
    have hcont : ContinuousWithinAt (fun a : Circle => e a) e.source z :=
      e.continuousOn.continuousWithinAt hzsrc
    have hwithin : Tendsto y atTop (𝓝[e.source] z) :=
      tendsto_nhdsWithin_iff.mpr ⟨hy, hyev⟩
    have hlim : Tendsto (fun n => e (y n)) atTop (𝓝 t₀) := by
      have h' : Tendsto (fun n => e (y n)) atTop (𝓝 (e z)) :=
        Filter.Tendsto.comp hcont hwithin
      rw [hez] at h'
      exact h'
    refine hlim.congr' ?_
    filter_upwards [hyev] with n hn
    show e (y n) = if h : y n ∈ e.source then e (y n) else _
    rw [dif_pos hn]
  -- apply the one-dimensional secant lemma
  have hmain := secant_dirC_limit hG hne hslim htlim hst
  refine hmain.congr' ?_
  filter_upwards with n
  show dirC ((curve γ) (s n) - (curve γ) (t n)) = dirC (γ (x n) - γ (y n))
  rw [curve, curve, hsexp n, htexp n]

/-- **`GoodC γ` is closed.** -/
theorem isClosed_GoodC (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ∞ γ) : IsClosed (GoodC γ) := by
  classical
  have hγc : Continuous γ := hγ.isImmersion.contMDiff.continuous
  have hinj : Function.Injective γ := hγ.isEmbedding.injective
  refine (isSeqClosed_iff_isClosed).mp ?_
  intro v w hv hlim
  -- nondegenerate witnesses of the collisions `v n`
  have hwit : ∀ n, ∃ p q : Circle × Circle, p.1 ≠ p.2 ∧ q.1 ≠ q.2 ∧
      midPair γ p = midPair γ q ∧ dirPair γ p = dirPair γ q + v n ∧
      lenPair γ p = lenPair γ q := by
    intro n
    have hu : v n ∈ GoodC γ := hv n
    simp only [GoodC, Set.mem_ofPred_eq] at hu
    obtain ⟨x, y, x', y', hxy, hx'y', heq⟩ := hu
    refine ⟨(x, y), (x', y'), hxy, hx'y', ?_, ?_, ?_⟩
    · have h := congrArg (fun z : (ℝ × ℝ) × UnitAddCircle × ℝ => z.1) heq
      simpa only [muOrd_eq, actC] using h
    · have h := congrArg (fun z : (ℝ × ℝ) × UnitAddCircle × ℝ => z.2.1) heq
      simpa only [muOrd_eq, actC] using h
    · have h := congrArg (fun z : (ℝ × ℝ) × UnitAddCircle × ℝ => z.2.2) heq
      simpa only [muOrd_eq, actC] using h
  choose p q hpne hqne hmid hdir hlen using hwit
  -- the configuration space is compact: pass to a convergent subsequence
  obtain ⟨tt, -, φ, hφmono, hφtend⟩ :=
    IsCompact.tendsto_subseq (s := Set.univ) (x := fun n => (v n, p n, q n))
      isCompact_univ (fun n => Set.mem_univ _)
  have hTp : Tendsto (fun n => p (φ n)) atTop (𝓝 tt.2.1) := by
    have h : Tendsto (fun t : ConfSpace => t.2.1) (𝓝 tt) (𝓝 tt.2.1) :=
      (continuous_fst.comp continuous_snd).tendsto tt
    exact h.comp hφtend
  have hTq : Tendsto (fun n => q (φ n)) atTop (𝓝 tt.2.2) := by
    have h : Tendsto (fun t : ConfSpace => t.2.2) (𝓝 tt) (𝓝 tt.2.2) :=
      (continuous_snd.comp continuous_snd).tendsto tt
    exact h.comp hφtend
  have hTv : Tendsto (fun n => v (φ n)) atTop (𝓝 tt.1) := by
    have h : Tendsto (fun t : ConfSpace => t.1) (𝓝 tt) (𝓝 tt.1) :=
      continuous_fst.tendsto tt
    exact h.comp hφtend
  have htt1 : tt.1 = w := tendsto_nhds_unique hTv (hlim.comp hφmono.tendsto_atTop)
  -- the midpoint and length equations pass to the limit
  have hmid_eq : midPair γ tt.2.1 = midPair γ tt.2.2 := by
    have h1 : Tendsto (fun n => midPair γ (p (φ n))) atTop (𝓝 (midPair γ tt.2.1)) :=
      ((continuous_midPair hγc).tendsto tt.2.1).comp hTp
    have h2 : Tendsto (fun n => midPair γ (q (φ n))) atTop (𝓝 (midPair γ tt.2.2)) :=
      ((continuous_midPair hγc).tendsto tt.2.2).comp hTq
    exact tendsto_nhds_unique h1 (h2.congr' (Eventually.of_forall fun n => (hmid (φ n)).symm))
  have hlen_eq : lenPair γ tt.2.1 = lenPair γ tt.2.2 := by
    have h1 : Tendsto (fun n => lenPair γ (p (φ n))) atTop (𝓝 (lenPair γ tt.2.1)) :=
      ((continuous_lenPair hγc).tendsto tt.2.1).comp hTp
    have h2 : Tendsto (fun n => lenPair γ (q (φ n))) atTop (𝓝 (lenPair γ tt.2.2)) :=
      ((continuous_lenPair hγc).tendsto tt.2.2).comp hTq
    exact tendsto_nhds_unique h1 (h2.congr' (Eventually.of_forall fun n => (hlen (φ n)).symm))
  by_cases hdeg : (tt.2.1).1 = (tt.2.1).2
  · -- the limiting chord degenerates
    have hpp0 : pairVec γ tt.2.1 = 0 := by
      have h : γ tt.2.1.1 = γ tt.2.1.2 := by rw [hdeg]
      simpa only [pairVec] using sub_eq_zero.mpr h
    have hlen0 : lenPair γ tt.2.1 = 0 := by simp only [lenPair, hpp0, eucNorm_zero']
    have hlen0' : lenPair γ tt.2.2 = 0 := by rw [← hlen_eq, hlen0]
    have hqq0 : pairVec γ tt.2.2 = 0 := by
      have h : eucNorm (pairVec γ tt.2.2) = 0 := by simpa only [lenPair] using hlen0'
      exact eucNorm_eq_zero.mp h
    have hqdeg : (tt.2.2).1 = (tt.2.2).2 := by
      have h : γ tt.2.2.1 = γ tt.2.2.2 := sub_eq_zero.mp (by simpa only [pairVec] using hqq0)
      exact hinj h
    have hmid1 : midPair γ tt.2.1 = γ tt.2.1.1 := by
      show (γ tt.2.1.1 + γ tt.2.1.2) / 2 = γ tt.2.1.1
      rw [hdeg]
      ext <;> simp
    have hmid2 : midPair γ tt.2.2 = γ tt.2.2.1 := by
      show (γ tt.2.2.1 + γ tt.2.2.2) / 2 = γ tt.2.2.1
      rw [hqdeg]
      ext <;> simp
    have hz1 : γ tt.2.1.1 = γ tt.2.2.1 := by rw [← hmid1, hmid_eq, hmid2]
    have hz_eq : tt.2.1.1 = tt.2.2.1 := hinj hz1
    obtain ⟨t₀, ht₀⟩ := Circle.exp_surjective tt.2.1.1
    have hx1 : Tendsto (fun n => (p (φ n)).1) atTop (𝓝 tt.2.1.1) :=
      (continuous_fst.tendsto tt.2.1).comp hTp
    have hx2 : Tendsto (fun n => (p (φ n)).2) atTop (𝓝 tt.2.1.1) := by
      have h : Tendsto (fun n => (p (φ n)).2) atTop (𝓝 (tt.2.1).2) :=
        (continuous_snd.tendsto tt.2.1).comp hTp
      rwa [← hdeg] at h
    have hy1 : Tendsto (fun n => (q (φ n)).1) atTop (𝓝 tt.2.1.1) := by
      have h : Tendsto (fun n => (q (φ n)).1) atTop (𝓝 (tt.2.2).1) :=
        (continuous_fst.tendsto tt.2.2).comp hTq
      rwa [← hz_eq] at h
    have hy2 : Tendsto (fun n => (q (φ n)).2) atTop (𝓝 tt.2.1.1) := by
      have h : Tendsto (fun n => (q (φ n)).2) atTop (𝓝 (tt.2.2).2) :=
        (continuous_snd.tendsto tt.2.2).comp hTq
      rwa [← hqdeg, ← hz_eq] at h
    have hA : Tendsto (fun n => dirPair γ (p (φ n))) atTop (𝓝 (dirC (deriv (curve γ) t₀))) := by
      have h := chord_dirC_limit γ hγ ht₀ hx1 hx2 (fun n => hpne (φ n))
      simpa only [dirPair, pairVec] using h
    have hB : Tendsto (fun n => dirPair γ (q (φ n))) atTop (𝓝 (dirC (deriv (curve γ) t₀))) := by
      have h := chord_dirC_limit γ hγ ht₀ hy1 hy2 (fun n => hqne (φ n))
      simpa only [dirPair, pairVec] using h
    have hv0 : tt.1 = 0 := by
      have h3 : Tendsto (fun n => dirPair γ (p (φ n)) - dirPair γ (q (φ n))) atTop
          (𝓝 (dirC (deriv (curve γ) t₀) - dirC (deriv (curve γ) t₀))) := hA.sub hB
      rw [sub_self] at h3
      have h3' : Tendsto (fun n => v (φ n)) atTop (𝓝 0) :=
        h3.congr' (Eventually.of_forall fun n => by
          show dirPair γ (p (φ n)) - dirPair γ (q (φ n)) = v (φ n)
          exact sub_eq_iff_eq_add.mpr (by rw [add_comm]; exact hdir (φ n)))
      exact tendsto_nhds_unique hTv h3'
    rw [← htt1, hv0]
    exact zero_mem_GoodC γ
  · -- the limiting chord is nondegenerate: the equations pass to the limit
    have hppnz : pairVec γ tt.2.1 ≠ 0 := by
      intro h
      exact hdeg (hinj (sub_eq_zero.mp h))
    have hlpos : 0 < lenPair γ tt.2.1 := by
      simpa only [lenPair] using eucNorm_pos hppnz
    have hlpos2 : 0 < lenPair γ tt.2.2 := by rw [← hlen_eq]; exact hlpos
    have hqqnz : pairVec γ tt.2.2 ≠ 0 := by
      intro h
      have h0 : lenPair γ tt.2.2 = 0 := by simp only [lenPair, h, eucNorm_zero']
      rw [h0] at hlpos2
      exact lt_irrefl 0 hlpos2
    have hqdeg : (tt.2.2).1 ≠ (tt.2.2).2 := by
      intro h
      exact hqqnz (by simp only [pairVec, h, sub_self])
    have hd1 : Tendsto (fun n => dirPair γ (p (φ n))) atTop (𝓝 (dirPair γ tt.2.1)) := by
      have hev : ∀ᶠ n in atTop, p (φ n) ∈ {r : Circle × Circle | pairVec γ r ≠ 0} :=
        hTp.eventually ((isOpen_ne.preimage (continuous_pairVec hγc)).mem_nhds hppnz)
      have htwi : Tendsto (fun n => p (φ n)) atTop
          (𝓝[{r : Circle × Circle | pairVec γ r ≠ 0}] tt.2.1) :=
        tendsto_nhdsWithin_iff.mpr ⟨hTp, hev⟩
      have hcont : Tendsto (dirPair γ) (𝓝[{r : Circle × Circle | pairVec γ r ≠ 0}] tt.2.1)
          (𝓝 (dirPair γ tt.2.1)) :=
        (continuousOn_dirPair hγc).continuousWithinAt hppnz
      have hcomp := Filter.Tendsto.comp hcont htwi
      rw [show (dirPair γ ∘ fun n => p (φ n)) = (fun n => dirPair γ (p (φ n))) from rfl] at hcomp
      exact hcomp
    have hd2 : Tendsto (fun n => dirPair γ (q (φ n))) atTop (𝓝 (dirPair γ tt.2.2)) := by
      have hev : ∀ᶠ n in atTop, q (φ n) ∈ {r : Circle × Circle | pairVec γ r ≠ 0} :=
        hTq.eventually ((isOpen_ne.preimage (continuous_pairVec hγc)).mem_nhds hqqnz)
      have htwi : Tendsto (fun n => q (φ n)) atTop
          (𝓝[{r : Circle × Circle | pairVec γ r ≠ 0}] tt.2.2) :=
        tendsto_nhdsWithin_iff.mpr ⟨hTq, hev⟩
      have hcont : Tendsto (dirPair γ) (𝓝[{r : Circle × Circle | pairVec γ r ≠ 0}] tt.2.2)
          (𝓝 (dirPair γ tt.2.2)) :=
        (continuousOn_dirPair hγc).continuousWithinAt hqqnz
      have hcomp := Filter.Tendsto.comp hcont htwi
      rw [show (dirPair γ ∘ fun n => q (φ n)) = (fun n => dirPair γ (q (φ n))) from rfl] at hcomp
      exact hcomp
    have hdireq : dirPair γ tt.2.1 = dirPair γ tt.2.2 + tt.1 := by
      have h3 : Tendsto (fun n => dirPair γ (q (φ n)) + v (φ n)) atTop
          (𝓝 (dirPair γ tt.2.2 + tt.1)) := hd2.add hTv
      exact tendsto_nhds_unique hd1 (h3.congr' (Eventually.of_forall fun n => (hdir (φ n)).symm))
    rw [← htt1]
    refine ⟨tt.2.1.1, tt.2.1.2, tt.2.2.1, tt.2.2.2, hdeg, hqdeg, ?_⟩
    rw [muOrd_eq, muOrd_eq, actC]
    exact Prod.ext hmid_eq (Prod.ext hdireq hlen_eq)

open Manifold in
open scoped Manifold ContDiff in
/-- The set of angles at which the configuration Möbius strip of `γ` misses its rotation is open. -/
theorem isOpen_Zc (γ : Circle → ℝ × ℝ) (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) :
    IsOpen (Work.Drive.Zc γ) := by
  rw [Zc_eq_compl]
  exact (isClosed_GoodC γ hγ).isOpen_compl

end Work.Drive
