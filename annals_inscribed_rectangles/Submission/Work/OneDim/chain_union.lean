import Mathlib
import Submission.Work.OneDim.ArcDefs
import Submission.Work.OneDim.reparam_arc
import Submission.Work.OneDim.interval_surj
import Submission.Work.OneDim.SeamTools
import Submission.Work.OneDim.ift_real

/-!
# The union of a chain of open arcs is an open arc

`Work.OneDim.chain_union`: if `c` is a nonempty family of open arcs of a smooth `1`-manifold `C`
(second countable, Hausdorff) which is totally ordered by inclusion, then `⋃₀ c` is an open arc.

The proof has four steps.

1. *Reduction to an increasing sequence.*  By second countability, `⋃₀ c` has a countable subcover by
   members of the chain (`chain_monotone_cover`), and the finite maxima of an enumeration of that
   countable subfamily form an increasing sequence `A : ℕ → Set C` of members of `c` with
   `⋃ n, A n = ⋃₀ c`.
2. *A countable family of compact sets covering `U`.*  Taking arbitrary parametrisations of the arcs
   `A n` and all their windows gives compact sets `K k` with `⋃ k, K k = U`.  Since every compact
   subset of `U` lies in some member of the chain (`exists_mem_of_compact_subset_sUnion`), one can
   pass to a subsequence `σ` with `K n ⊆ A (σ n)`.
3. *A recursion of compatible parametrisations with growing windows.*  A parametrisation `γ 0` of
   `A (σ 0)` is chosen, together with a window `Icc (-N 0) N 0` containing `K 0`
   (`exists_Icc_of_compact_subset_range`).  Given `γ n` parametrising `A (σ n)` and a window
   containing `K n`, one extends it to a parametrisation `γ (n+1)` of `A (σ (n+1))` agreeing with
   `γ n` on `Icc (-N n) (N n)` (`arc_step_extend`, which rests on the analytic lemma
   `exists_diffeomorph_eqOn_Icc`), and then chooses `N (n+1) > N n` so large that `K (n+1)` lies in
   the new window.
4. *Gluing.*  `γ t := γ (m t) t`, where `m t` is the least index with `|t| ≤ N (m t)`, is well
   defined by the compatibility of successive parametrisations, is an injective local
   diffeomorphism, and its range is `⋃ k, K k = U`.

## Main results

* `Work.OneDim.chain_monotone_cover`
* `Work.OneDim.exists_diffeomorph_eqOn_Icc`
* `Work.OneDim.arc_step_extend`
* `Work.OneDim.chain_union`
-/

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

namespace Work.OneDim

/-! ## 1. Reduction of a chain to an increasing sequence -/

/-- **A chain of open sets in a second countable space is covered by an increasing sequence of its
members.** -/
theorem chain_monotone_cover {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    {c : Set (Set X)} (hc : ∀ A ∈ c, IsOpen A) (hchain : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    ∃ A : ℕ → Set X, (∀ n, A n ∈ c) ∧ Monotone A ∧ ⋃ n, A n = ⋃₀ c := by
  classical
  obtain ⟨B, hBc, -, hBbasis⟩ := TopologicalSpace.exists_countable_basis X
  let P : Set (Set X) := {V | V ∈ B ∧ ∃ U ∈ c, V ⊆ U}
  have hPc : P.Countable := hBc.mono (fun V hV => hV.1)
  haveI : Countable P := hPc.to_subtype
  let f : P → Set X := fun V => Classical.choose V.2.2
  have hf : ∀ V : P, f V ∈ c ∧ (V : Set X) ⊆ f V := fun V => Classical.choose_spec V.2.2
  have hrangesub : Set.range f ⊆ c := by rintro _ ⟨V, rfl⟩; exact (hf V).1
  have hUn : ⋃₀ (Set.range f) = ⋃₀ c := by
    apply le_antisymm
    · exact sUnion_subset (fun A hA => subset_sUnion_of_mem (hrangesub hA))
    · rintro x ⟨U, hUc, hxU⟩
      obtain ⟨V, hVB, hxV, hVU⟩ := hBbasis.exists_subset_of_mem_open hxU (hc U hUc)
      refine mem_sUnion.mpr ⟨f ⟨V, hVB, U, hUc, hVU⟩, Set.mem_range_self _, ?_⟩
      exact (hf ⟨V, hVB, U, hUc, hVU⟩).2 hxV
  obtain ⟨A₀, hA₀⟩ := hne
  let S : Set (Set X) := Set.range f ∪ {A₀}
  have hSdef : S = Set.range f ∪ {A₀} := rfl
  have hSc : S.Countable := Set.Countable.union (countable_range f) (countable_singleton A₀)
  have hSne : S.Nonempty := ⟨A₀, Or.inr rfl⟩
  have hSsub : S ⊆ c := by
    intro A hA
    rw [hSdef] at hA
    rcases hA with h | h
    · exact hrangesub h
    · rw [Set.mem_singleton_iff] at h; rw [h]; exact hA₀
  obtain ⟨g, hg⟩ := hSc.exists_eq_range hSne
  let A : ℕ → Set X := fun n => Nat.rec (g 0) (fun k ih => ih ∪ g (k+1)) n
  have hA0 : A 0 = g 0 := rfl
  have hAsucc : ∀ n, A (n+1) = A n ∪ g (n+1) := fun n => rfl
  have hgS : ∀ n, g n ∈ S := fun n => by rw [hg]; exact Set.mem_range_self n
  have hAmem : ∀ n, A n ∈ S := by
    intro n
    induction n with
    | zero => rw [hA0]; exact hgS 0
    | succ n ih =>
      rw [hAsucc n]
      rcases hchain.total (hSsub ih) (hSsub (hgS (n+1))) with h | h
      · rw [Set.union_eq_right.mpr h]; exact hgS (n+1)
      · rw [Set.union_eq_left.mpr h]; exact ih
  have hAle : ∀ n, A n ⊆ A (n+1) := by
    intro n; rw [hAsucc n]; exact subset_union_left
  have hAmono : Monotone A := monotone_nat_of_le_succ hAle
  have hgkA : ∀ k, g k ⊆ A k := by
    intro k
    induction k with
    | zero => rw [hA0]
    | succ k ih => rw [hAsucc k]; exact subset_union_right
  have hAS : ⋃ n, A n = ⋃₀ S := by
    apply le_antisymm
    · exact iUnion_subset (fun n => subset_sUnion_of_mem (hAmem n))
    · intro x hx
      rw [hg] at hx
      obtain ⟨s, hs, hxs⟩ := mem_sUnion.mp hx
      obtain ⟨k, rfl⟩ := hs
      exact mem_iUnion.mpr ⟨k, hgkA k hxs⟩
  have hSunion : ⋃₀ S = ⋃₀ c := by
    rw [hSdef, sUnion_union, sUnion_singleton, hUn]
    exact Set.union_eq_left.mpr (subset_sUnion_of_mem hA₀)
  exact ⟨A, fun n => hSsub (hAmem n), hAmono, hAS.trans hSunion⟩


/-- The smooth gadget `z ↦ z * smoothTransition z`: nonnegative, monotone, vanishing on `(-∞,0]`,
equal to the identity on `[1,∞)`. -/
def smoothGad (z : ℝ) : ℝ := z * Real.smoothTransition z

lemma smoothGad_of_nonpos {z : ℝ} (hz : z ≤ 0) : smoothGad z = 0 := by
  simp [smoothGad, Real.smoothTransition.zero_of_nonpos hz]

lemma smoothGad_nonneg (z : ℝ) : 0 ≤ smoothGad z := by
  rcases le_total 0 z with h | h
  · exact mul_nonneg h (Real.smoothTransition.nonneg z)
  · rw [smoothGad_of_nonpos h]

lemma smoothGad_mono : Monotone smoothGad := by
  intro z w hzw
  rcases le_total 0 z with hz | hz
  · exact mul_le_mul hzw (Real.smoothTransition.monotone hzw) (Real.smoothTransition.nonneg z)
      (le_trans hz hzw)
  · rw [smoothGad_of_nonpos hz]; exact smoothGad_nonneg w

lemma contDiff_smoothGad : ContDiff ℝ ∞ smoothGad :=
  contDiff_id.mul Real.smoothTransition.contDiff

lemma smoothGad_eq_self {z : ℝ} (hz : 1 ≤ z) : smoothGad z = z := by
  simp [smoothGad, Real.smoothTransition.one_of_one_le hz]

/-- A `C^∞` local diffeomorphism `ℝ → ℝ` has nonzero derivative everywhere. -/
lemma deriv_ne_zero_of_isLocalDiffeomorphAt {f : ℝ → ℝ} {x : ℝ}
    (h : IsLocalDiffeomorphAt 𝓘(ℝ) 𝓘(ℝ) sm f x) : deriv f x ≠ 0 := by
  intro h0
  have hn : sm ≠ 0 := by decide
  set g : ℝ → ℝ := fun y => h.localInverse y with hgdef
  have heq : g ∘ f =ᶠ[𝓝 x] id := h.localInverse_eventuallyEq_left
  have hg_diff : DifferentiableAt ℝ g (f x) := by
    have : ContDiffAt ℝ sm g (f x) := by
      rw [hgdef]; exact (contMDiffAt_iff_contDiffAt).mp h.localInverse_contMDiffAt
    exact this.differentiableAt hn
  have hf_diff : DifferentiableAt ℝ f x := by
    have : ContDiffAt ℝ sm f x := (contMDiffAt_iff_contDiffAt).mp h.contMDiffAt
    exact this.differentiableAt hn
  have h1 : fderiv ℝ (g ∘ f) x = 1 := by
    rw [heq.fderiv_eq, fderiv_id]
    exact ContinuousLinearMap.ext_ring (by simp)
  have h2 : (fderiv ℝ g (f x)).comp (fderiv ℝ f x) = 1 := by
    rw [← fderiv_comp x hg_diff hf_diff, h1]
  have h3 : ((fderiv ℝ g (f x)).comp (fderiv ℝ f x)) 1 = (1 : ℝ →L[ℝ] ℝ) 1 := by rw [h2]
  simp only [ContinuousLinearMap.comp_apply] at h3
  rw [show (fderiv ℝ f x) 1 = deriv f x from rfl, h0, map_zero] at h3
  exact one_ne_zero h3.symm

/-- **Extending a local diffeomorphism `ℝ → ℝ` to a global diffeomorphism on a window.** -/
theorem exists_diffeomorph_eqOn_Icc {u : ℝ → ℝ} (hinj : Function.Injective u)
    (hld : IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) sm u) (N : ℝ) :
    ∃ v : ℝ → ℝ, Function.Bijective v ∧
      IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) sm v ∧
      Set.EqOn v u (Set.Icc (-N) N) := by
  classical
  have hcont : Continuous u := hld.contMDiff.continuous
  have hIopen : IsOpen (Set.range u) := hld.isOpen_range
  have hIpre : IsPreconnected (Set.range u) := isPreconnected_range hcont
  have hIne : (Set.range u).Nonempty := ⟨u 0, Set.mem_range_self 0⟩
  obtain ⟨e, heinj, held, herange⟩ := interval_surj hIopen hIpre hIne
  have hecont : Continuous e := held.contMDiff.continuous
  have hederiv : ∀ y, deriv e y ≠ 0 := fun y => deriv_ne_zero_of_isLocalDiffeomorphAt (held y)
  have hecu : ContDiff ℝ ∞ e := (contMDiff_iff_contDiff).mp held.contMDiff
  have hinv_ld : ∀ y ∈ Set.range e,
      IsLocalDiffeomorphAt 𝓘(ℝ) 𝓘(ℝ) sm (Function.invFun e) y := by
    rintro y ⟨t, rfl⟩
    refine isLocalDiffeomorphAt_congr (held t).localInverse_isLocalDiffeomorphAt ?_
    refine Filter.eventuallyEq_of_mem
      ((held t).localInverse_open_source.mem_nhds (held t).localInverse_mem_source) ?_
    intro y' hy'
    have h1 : e ((held t).localInverse y') = y' := (held t).localInverse_right_inv hy'
    exact heinj (h1.trans (Function.invFun_eq ⟨_, h1⟩).symm)
  set g : ℝ → ℝ := Function.invFun e ∘ u with hgdef
  have hge : ∀ t, e (g t) = u t := by
    intro t
    have : u t ∈ Set.range e := by rw [herange]; exact Set.mem_range_self t
    exact Function.invFun_eq this
  have hginj : Function.Injective g := by
    intro a b hab
    refine hinj ?_
    rw [← hge a, ← hge b, hab]
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : e y ∈ Set.range u := by rw [← herange]; exact ⟨y, rfl⟩
    obtain ⟨t, ht⟩ := hy
    refine ⟨t, ?_⟩
    show Function.invFun e (u t) = y
    rw [ht, Function.leftInverse_invFun heinj y]
  have hgld : IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) sm g := by
    intro t
    have h1 : IsLocalDiffeomorphAt 𝓘(ℝ) 𝓘(ℝ) sm (Function.invFun e) (u t) :=
      hinv_ld (u t) (by rw [herange]; exact Set.mem_range_self t)
    exact IsLocalDiffeomorphAt.comp (I := 𝓘(ℝ)) (J := 𝓘(ℝ)) (K := 𝓘(ℝ)) (M := ℝ) (N := ℝ) (P := ℝ)
      (n := sm) (g := Function.invFun e) (hld t) h1
  have hgcont : Continuous g := hgld.contMDiff.continuous
  set K : Set ℝ := g '' Set.Icc (-N) N with hKdef
  have hKcomp : IsCompact K := isCompact_Icc.image hgcont
  have hKsub : ∀ {y : ℝ}, y ∈ K → y ∈ Set.Icc (sInf K) (sSup K) :=
    fun hy => ⟨csInf_le hKcomp.bddBelow hy, le_csSup hKcomp.bddAbove hy⟩
  have final : ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w →
      IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) sm w → Function.Bijective w → (∀ y ∈ K, w y = e y) →
      ∃ v : ℝ → ℝ, Function.Bijective v ∧ IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) sm v ∧
        Set.EqOn v u (Set.Icc (-N) N) := by
    intro w hwc hwld hwbij hwK
    refine ⟨w ∘ g, ⟨hwbij.1.comp hginj, hwbij.2.comp hgsurj⟩, ?_, ?_⟩
    · intro t
      exact IsLocalDiffeomorphAt.comp (I := 𝓘(ℝ)) (J := 𝓘(ℝ)) (K := 𝓘(ℝ)) (M := ℝ) (N := ℝ)
        (P := ℝ) (n := sm) (g := w) (hgld t) (hwld (g t))
    · intro t ht
      show w (g t) = u t
      rw [hwK (g t) ⟨t, ht, rfl⟩, hge t]
  have surj_of_limits : ∀ w : ℝ → ℝ, Continuous w → (∀ m : ℝ, ∃ y₀, ∀ y ≤ y₀, w y < m) →
      (∀ m : ℝ, ∃ y₀, ∀ y, y₀ ≤ y → m < w y) → Function.Surjective w := by
    intro w hwc hbot htop m
    obtain ⟨y₁, hy₁⟩ := hbot m
    obtain ⟨y₂, hy₂⟩ := htop m
    have h1 : y₁ ≤ max y₂ y₁ := le_max_right _ _
    have h2 : w y₁ < m := hy₁ y₁ le_rfl
    have h3 : m < w (max y₂ y₁) := hy₂ (max y₂ y₁) (le_max_left _ _)
    obtain ⟨y, -, hy⟩ := intermediate_value_Icc h1 hwc.continuousOn
      (show m ∈ Set.Icc (w y₁) (w (max y₂ y₁)) from ⟨h2.le, h3.le⟩)
    exact ⟨y, hy⟩
  have surj_of_limits' : ∀ w : ℝ → ℝ, Continuous w → (∀ m : ℝ, ∃ y₀, ∀ y ≤ y₀, m < w y) →
      (∀ m : ℝ, ∃ y₀, ∀ y, y₀ ≤ y → w y < m) → Function.Surjective w := by
    intro w hwc htop hbot m
    obtain ⟨y₁, hy₁⟩ := htop m
    obtain ⟨y₂, hy₂⟩ := hbot m
    have h1 : y₁ ≤ max y₁ y₂ := le_max_left _ _
    have h2 : m < w y₁ := hy₁ y₁ le_rfl
    have h3 : w (max y₁ y₂) < m := hy₂ (max y₁ y₂) (le_max_right _ _)
    obtain ⟨y, -, hy⟩ := intermediate_value_Icc' h1 hwc.continuousOn
      (show m ∈ Set.Icc (w (max y₁ y₂)) (w y₁) from ⟨h3.le, h2.le⟩)
    exact ⟨y, hy⟩
  rcases hecont.strictMono_of_inj heinj with hmono | hanti
  · set c : ℝ := min (sInf K) (sSup K) with hcdef
    set d : ℝ := max (sInf K) (sSup K) with hddef
    have hcd : c ≤ d := by rw [hcdef, hddef]; exact min_le_max
    have hcE : c ≤ sSup K := by rw [hcdef]; exact min_le_right _ _
    have hdE : sInf K ≤ d := by rw [hddef]; exact le_max_left _ _
    have hKcd : ∀ {y : ℝ}, y ∈ K → y ∈ Set.Icc c d := by
      intro y hy
      obtain ⟨h1, h2⟩ := hKsub hy
      exact ⟨le_trans (min_le_left _ _) h1, le_trans h2 (le_max_right _ _)⟩
    set w : ℝ → ℝ := fun y => e y + smoothGad (y - d) - smoothGad (c - y) with hwdef
    have hwsmooth : ContDiff ℝ ∞ w := by
      rw [hwdef]
      exact (hecu.add (contDiff_smoothGad.comp (contDiff_id.sub contDiff_const))).sub
        (contDiff_smoothGad.comp (contDiff_const.sub contDiff_id))
    have hwmono : StrictMono w := by
      intro y y' hyy
      have h1 : e y < e y' := hmono hyy
      have h2 : smoothGad (y - d) ≤ smoothGad (y' - d) := smoothGad_mono (by linarith)
      have h3 : smoothGad (c - y') ≤ smoothGad (c - y) := smoothGad_mono (by linarith)
      show e y + smoothGad (y - d) - smoothGad (c - y) <
        e y' + smoothGad (y' - d) - smoothGad (c - y')
      linarith
    have hwK : ∀ y ∈ K, w y = e y := by
      intro y hy
      obtain ⟨h1, h2⟩ := hKcd hy
      have h3 : y - d ≤ 0 := by linarith
      have h4 : c - y ≤ 0 := by linarith
      show e y + smoothGad (y - d) - smoothGad (c - y) = e y
      rw [smoothGad_of_nonpos h3, smoothGad_of_nonpos h4]
      ring
    have hwbot : ∀ m : ℝ, ∃ y₀, ∀ y ≤ y₀, w y < m := by
      intro m
      refine ⟨min (c - 1) (m - (e (sSup K) - c) - 1), fun y hy => ?_⟩
      have hy1 : y ≤ c - 1 := le_trans hy (min_le_left _ _)
      have hy2 : y ≤ m - (e (sSup K) - c) - 1 := le_trans hy (min_le_right _ _)
      have h1 : y ≤ sSup K := by linarith
      have h2 : e y ≤ e (sSup K) := hmono.monotone h1
      have h3 : smoothGad (y - d) = 0 := smoothGad_of_nonpos (by linarith)
      have h4 : smoothGad (c - y) = c - y := smoothGad_eq_self (by linarith)
      have h5 : w y = e y - (c - y) := by
        show e y + smoothGad (y - d) - smoothGad (c - y) = e y - (c - y)
        rw [h3, h4]; ring
      rw [h5]; linarith
    have hwtop : ∀ m : ℝ, ∃ y₀, ∀ y, y₀ ≤ y → m < w y := by
      intro m
      refine ⟨max (d + 1) (m - e (sInf K) + d + 1), fun y hy => ?_⟩
      have hy1 : d + 1 ≤ y := le_trans (le_max_left _ _) hy
      have hy2 : m - e (sInf K) + d + 1 ≤ y := le_trans (le_max_right _ _) hy
      have h1 : sInf K ≤ y := by linarith
      have h2 : e (sInf K) ≤ e y := hmono.monotone h1
      have h3 : smoothGad (y - d) = y - d := smoothGad_eq_self (by linarith)
      have h4 : smoothGad (c - y) = 0 := smoothGad_of_nonpos (by linarith)
      have h5 : e (sInf K) + (y - d) ≤ w y := by
        show e (sInf K) + (y - d) ≤ e y + smoothGad (y - d) - smoothGad (c - y)
        rw [h3, h4]; linarith
      linarith
    have hwsurj : Function.Surjective w := surj_of_limits w hwsmooth.continuous hwbot hwtop
    have hwbij : Function.Bijective w := ⟨hwmono.injective, hwsurj⟩
    have hwld : IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) sm w := by
      refine ift_real hwsmooth (fun y => ?_)
      have hde : 0 < deriv e y := by
        have h1 : 0 ≤ deriv e y := hmono.monotone.deriv_nonneg
        exact lt_of_le_of_ne h1 (hederiv y).symm
      have hC : Monotone (fun y : ℝ => smoothGad (y - d) - smoothGad (c - y)) := by
        intro a b hab
        have h1 : smoothGad (a - d) ≤ smoothGad (b - d) := smoothGad_mono (by linarith)
        have h2 : smoothGad (c - b) ≤ smoothGad (c - a) := smoothGad_mono (by linarith)
        linarith
      have hdC : 0 ≤ deriv (fun y : ℝ => smoothGad (y - d) - smoothGad (c - y)) y := hC.deriv_nonneg
      have hdiff : deriv w y = deriv e y
          + deriv (fun y : ℝ => smoothGad (y - d) - smoothGad (c - y)) y := by
        have hA : DifferentiableAt ℝ e y := (hecu.differentiable (by decide)).differentiableAt
        have hB : DifferentiableAt ℝ (fun y : ℝ => smoothGad (y - d)) y :=
          ((contDiff_smoothGad.comp (contDiff_id.sub contDiff_const)).differentiable
            (by decide)).differentiableAt
        have hB2 : DifferentiableAt ℝ (fun y : ℝ => smoothGad (c - y)) y :=
          ((contDiff_smoothGad.comp (contDiff_const.sub contDiff_id)).differentiable
            (by decide)).differentiableAt
        change deriv ((e + fun y : ℝ => smoothGad (y - d)) - fun y : ℝ => smoothGad (c - y)) y
          = deriv e y + deriv ((fun y : ℝ => smoothGad (y - d)) - fun y : ℝ => smoothGad (c - y)) y
        rw [deriv_sub (hA.add hB) hB2, deriv_add hA hB, deriv_sub hB hB2]
        ring
      rw [hdiff]; linarith
    exact final w hwsmooth hwld hwbij hwK
  · set c : ℝ := min (sInf K) (sSup K) with hcdef
    set d : ℝ := max (sInf K) (sSup K) with hddef
    have hcd : c ≤ d := by rw [hcdef, hddef]; exact min_le_max
    have hcE : c ≤ sSup K := by rw [hcdef]; exact min_le_right _ _
    have hdE : sInf K ≤ d := by rw [hddef]; exact le_max_left _ _
    have hKcd : ∀ {y : ℝ}, y ∈ K → y ∈ Set.Icc c d := by
      intro y hy
      obtain ⟨h1, h2⟩ := hKsub hy
      exact ⟨le_trans (min_le_left _ _) h1, le_trans h2 (le_max_right _ _)⟩
    set w : ℝ → ℝ := fun y => e y + smoothGad (c - y) - smoothGad (y - d) with hwdef
    have hwsmooth : ContDiff ℝ ∞ w := by
      rw [hwdef]
      exact (hecu.add (contDiff_smoothGad.comp (contDiff_const.sub contDiff_id))).sub
        (contDiff_smoothGad.comp (contDiff_id.sub contDiff_const))
    have hwanti : StrictAnti w := by
      intro y y' hyy
      have h1 : e y' < e y := hanti hyy
      have h2 : smoothGad (c - y') ≤ smoothGad (c - y) := smoothGad_mono (by linarith)
      have h3 : smoothGad (y - d) ≤ smoothGad (y' - d) := smoothGad_mono (by linarith)
      show e y' + smoothGad (c - y') - smoothGad (y' - d) <
        e y + smoothGad (c - y) - smoothGad (y - d)
      linarith
    have hwK : ∀ y ∈ K, w y = e y := by
      intro y hy
      obtain ⟨h1, h2⟩ := hKcd hy
      have h3 : c - y ≤ 0 := by linarith
      have h4 : y - d ≤ 0 := by linarith
      show e y + smoothGad (c - y) - smoothGad (y - d) = e y
      rw [smoothGad_of_nonpos h3, smoothGad_of_nonpos h4]
      ring
    have hwtop : ∀ m : ℝ, ∃ y₀, ∀ y ≤ y₀, m < w y := by
      intro m
      refine ⟨min (c - 1) (e c + c - m - 1), fun y hy => ?_⟩
      have hy1 : y ≤ c - 1 := le_trans hy (min_le_left _ _)
      have hy2 : y ≤ e c + c - m - 1 := le_trans hy (min_le_right _ _)
      have h1 : y ≤ c := by linarith
      have h2 : e c ≤ e y := hanti.antitone h1
      have h3 : smoothGad (c - y) = c - y := smoothGad_eq_self (by linarith)
      have h4 : smoothGad (y - d) = 0 := smoothGad_of_nonpos (by linarith)
      have h5 : e c + (c - y) ≤ w y := by
        show e c + (c - y) ≤ e y + smoothGad (c - y) - smoothGad (y - d)
        rw [h3, h4]; linarith
      linarith
    have hwbot : ∀ m : ℝ, ∃ y₀, ∀ y, y₀ ≤ y → w y < m := by
      intro m
      refine ⟨max (d + 1) (e d + d - m + 1), fun y hy => ?_⟩
      have hy1 : d + 1 ≤ y := le_trans (le_max_left _ _) hy
      have hy2 : e d + d - m + 1 ≤ y := le_trans (le_max_right _ _) hy
      have h1 : d ≤ y := by linarith
      have h2 : e y ≤ e d := hanti.antitone h1
      have h3 : smoothGad (c - y) = 0 := smoothGad_of_nonpos (by linarith)
      have h4 : smoothGad (y - d) = y - d := smoothGad_eq_self (by linarith)
      have h5 : w y = e y - (y - d) := by
        show e y + smoothGad (c - y) - smoothGad (y - d) = e y - (y - d)
        rw [h3, h4]; ring
      rw [h5]; linarith
    have hwsurj : Function.Surjective w :=
      surj_of_limits' w hwsmooth.continuous hwtop hwbot
    have hwbij : Function.Bijective w := ⟨hwanti.injective, hwsurj⟩
    have hwld : IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) sm w := by
      refine ift_real hwsmooth (fun y => ?_)
      have hde : deriv e y < 0 := by
        have h1 : deriv e y ≤ 0 := hanti.antitone.deriv_nonpos
        exact lt_of_le_of_ne h1 (hederiv y)
      have hC : Antitone (fun y : ℝ => smoothGad (c - y) - smoothGad (y - d)) := by
        intro a b hab
        have h1 : smoothGad (c - b) ≤ smoothGad (c - a) := smoothGad_mono (by linarith)
        have h2 : smoothGad (a - d) ≤ smoothGad (b - d) := smoothGad_mono (by linarith)
        linarith
      have hdC : deriv (fun y : ℝ => smoothGad (c - y) - smoothGad (y - d)) y ≤ 0 := hC.deriv_nonpos
      have hdiff : deriv w y = deriv e y
          + deriv (fun y : ℝ => smoothGad (c - y) - smoothGad (y - d)) y := by
        have hA : DifferentiableAt ℝ e y := (hecu.differentiable (by decide)).differentiableAt
        have hB : DifferentiableAt ℝ (fun y : ℝ => smoothGad (c - y)) y :=
          ((contDiff_smoothGad.comp (contDiff_const.sub contDiff_id)).differentiable
            (by decide)).differentiableAt
        have hB2 : DifferentiableAt ℝ (fun y : ℝ => smoothGad (y - d)) y :=
          ((contDiff_smoothGad.comp (contDiff_id.sub contDiff_const)).differentiable
            (by decide)).differentiableAt
        change deriv ((e + fun y : ℝ => smoothGad (c - y)) - fun y : ℝ => smoothGad (y - d)) y
          = deriv e y + deriv ((fun y : ℝ => smoothGad (c - y)) - fun y : ℝ => smoothGad (y - d)) y
        rw [deriv_sub (hA.add hB) hB2, deriv_add hA hB, deriv_sub hB hB2]
        ring
      rw [hdiff]; linarith
    exact final w hwsmooth hwld hwbij hwK


/-- The inverse of an injective local diffeomorphism `ℝ → C` is a local diffeomorphism at points of
its range. -/
lemma isLocalDiffeomorphAt_invFun {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C]
    [IsManifold I1 sm C] {β : ℝ → C} (hβinj : Function.Injective β)
    (hβld : IsLocalDiffeomorph 𝓘(ℝ) I1 sm β) :
    ∀ y ∈ Set.range β, IsLocalDiffeomorphAt I1 𝓘(ℝ) sm (Function.invFun β) y := by
  rintro y ⟨t, rfl⟩
  refine isLocalDiffeomorphAt_congr (hβld t).localInverse_isLocalDiffeomorphAt ?_
  refine Filter.eventuallyEq_of_mem
    ((hβld t).localInverse_open_source.mem_nhds (hβld t).localInverse_mem_source) ?_
  intro y' hy'
  have h1 : β ((hβld t).localInverse y') = y' := (hβld t).localInverse_right_inv hy'
  exact hβinj (h1.trans (Function.invFun_eq ⟨_, h1⟩).symm)

/-- **Extending a parametrisation of an arc across a larger arc.**  If `γ : ℝ → C` is an injective
local diffeomorphism whose range is contained in the open arc `B`, then for every `N` there is a
parametrisation of all of `B` which agrees with `γ` on `[-N, N]`. -/
theorem arc_step_extend {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C]
    [IsManifold I1 sm C] {B : Set C} (hB : IsOpenArc B) {γ : ℝ → C}
    (hinj : Function.Injective γ) (hld : IsLocalDiffeomorph 𝓘(ℝ) I1 sm γ)
    (hrange : Set.range γ ⊆ B) (N : ℝ) :
    ∃ γ' : ℝ → C, Function.Injective γ' ∧ IsLocalDiffeomorph 𝓘(ℝ) I1 sm γ' ∧
      Set.range γ' = B ∧ Set.EqOn γ' γ (Set.Icc (-N) N) := by
  classical
  obtain ⟨β, hβinj, hβld, hβrange⟩ := hB
  have hβu : ∀ t, β (Function.invFun β (γ t)) = γ t := by
    intro t
    have h : γ t ∈ B := hrange (Set.mem_range_self t)
    rw [hβrange] at h
    exact Function.invFun_eq h
  have hu_inj : Function.Injective (Function.invFun β ∘ γ) := by
    intro a b hab
    have h : β ((Function.invFun β ∘ γ) a) = β ((Function.invFun β ∘ γ) b) := by rw [hab]
    rw [Function.comp_apply, Function.comp_apply, hβu a, hβu b] at h
    exact hinj h
  have hu_ld : IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) sm (Function.invFun β ∘ γ) := by
    intro t
    have h1 : IsLocalDiffeomorphAt I1 𝓘(ℝ) sm (Function.invFun β) (γ t) :=
      isLocalDiffeomorphAt_invFun hβinj hβld (γ t)
        (by rw [← hβrange]; exact hrange (Set.mem_range_self t))
    exact IsLocalDiffeomorphAt.comp (I := 𝓘(ℝ)) (J := I1) (K := 𝓘(ℝ)) (M := ℝ) (N := C) (P := ℝ)
      (n := sm) (g := Function.invFun β) (hld t) h1
  obtain ⟨v, hvbij, hvld, hveq⟩ := exists_diffeomorph_eqOn_Icc hu_inj hu_ld N
  refine ⟨β ∘ v, hβinj.comp hvbij.1, ?_, ?_, ?_⟩
  · intro t
    exact IsLocalDiffeomorphAt.comp (I := 𝓘(ℝ)) (J := 𝓘(ℝ)) (K := I1) (M := ℝ) (N := ℝ) (P := C)
      (n := sm) (g := β) (hvld t) (hβld (v t))
  · rw [Set.range_comp, hvbij.2.range_eq, Set.image_univ, ← hβrange]
  · intro t ht
    show β (v t) = γ t
    rw [hveq ht, Function.comp_apply, hβu t]

/-- **A compact subset of the range of an open map `ℝ → C` is contained in the image of a
window.** -/
lemma exists_Icc_of_compact_subset_range {C : Type*} [TopologicalSpace C] {γ : ℝ → C}
    (hopen : IsOpenMap γ) {K : Set C} (hK : IsCompact K) (hsub : K ⊆ Set.range γ) :
    ∃ B : ℝ, 0 ≤ B ∧ K ⊆ γ '' Set.Icc (-B) B := by
  classical
  have hne : ∀ x : K, ∃ t : ℝ, γ t = (x : C) := fun x => hsub x.2
  choose t ht using hne
  have hcov : K ⊆ ⋃ x : K, γ '' Metric.ball (t x) 1 := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, t ⟨y, hy⟩, Metric.mem_ball_self zero_lt_one, ht ⟨y, hy⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => γ '' Metric.ball (t x) 1)
    (fun x => hopen _ Metric.isOpen_ball) hcov
  refine ⟨(∑ x ∈ s, (|t x| + 1)) + 1, by positivity, fun y hy => ?_⟩
  obtain ⟨x, hxs, u, hu, rfl⟩ := mem_iUnion₂.mp (hs hy)
  have h1 : |u - t x| < 1 := by
    have h := Metric.mem_ball.mp hu
    rwa [Real.dist_eq] at h
  have h2 : |t x| + 1 ≤ (∑ x ∈ s, (|t x| + 1)) + 1 := by
    have h3 : |t x| + 1 ≤ ∑ x ∈ s, (|t x| + 1) :=
      Finset.single_le_sum (f := fun x => |t x| + 1) (fun i _ => by positivity) hxs
    linarith
  have h4 : |u| ≤ |u - t x| + |t x| := by
    have h := abs_add_le (u - t x) (t x)
    rwa [sub_add_cancel] at h
  have h5 : |u| < (∑ x ∈ s, (|t x| + 1)) + 1 := by linarith
  exact ⟨u, ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩, rfl⟩

/-- **A compact subset of the union of a chain of open sets is contained in a member of the
chain.** -/
lemma exists_mem_of_compact_subset_sUnion {C : Type*} [TopologicalSpace C]
    {c : Set (Set C)} (hco : ∀ A ∈ c, IsOpen A) (hchain : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    {K : Set C} (hK : IsCompact K) (hKc : K ⊆ ⋃₀ c) : ∃ M ∈ c, K ⊆ M := by
  classical
  have hcov : K ⊆ ⋃ P : {P : Set C // P ∈ c}, (P : Set C) := by
    intro x hx
    obtain ⟨P, hPc, hxP⟩ := mem_sUnion.mp (hKc hx)
    exact mem_iUnion.mpr ⟨⟨P, hPc⟩, hxP⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun P : {P : Set C // P ∈ c} => (P : Set C))
    (fun P => hco P.1 P.2) hcov
  have hmax : ∀ s : Finset {P : Set C // P ∈ c}, ∃ M ∈ c, ∀ P ∈ s, (P : Set C) ⊆ M := by
    intro s
    induction s using Finset.induction with
    | empty => obtain ⟨A₀, hA₀⟩ := hne; exact ⟨A₀, hA₀, by simp⟩
    | insert P s hPs ih =>
      obtain ⟨M, hMc, hMs⟩ := ih
      rcases hchain.total hMc P.2 with h | h
      · exact ⟨P.1, P.2, fun Q hQ => by
          rcases Finset.mem_insert.mp hQ with rfl | hQ'
          · exact subset_rfl
          · exact (hMs Q hQ').trans h⟩
      · exact ⟨M, hMc, fun Q hQ => by
          rcases Finset.mem_insert.mp hQ with rfl | hQ'
          · exact h
          · exact hMs Q hQ'⟩
  obtain ⟨M, hMc, hMs⟩ := hmax s
  refine ⟨M, hMc, fun x hx => ?_⟩
  obtain ⟨P, hPs, hxP⟩ := mem_iUnion₂.mp (hs hx)
  exact hMs P hPs hxP

/-- **The union of a nonempty chain of open arcs is an open arc.** -/
theorem chain_union {C : Type*} [TopologicalSpace C] [ChartedSpace Work.OneDim.E1 C]
    [IsManifold Work.OneDim.I1 Work.OneDim.sm C] [T2Space C] [SecondCountableTopology C]
    {c : Set (Set C)} (hc : ∀ A ∈ c, Work.OneDim.IsOpenArc A)
    (hchain : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    Work.OneDim.IsOpenArc (⋃₀ c) := by
  classical
  have hco : ∀ A ∈ c, IsOpen A := fun A hA => (hc A hA).isOpen
  -- 1. an increasing sequence of members of the chain covering `U`
  obtain ⟨A, hAc, hAmono, hAcov⟩ := chain_monotone_cover hco hchain hne
  -- 2. arbitrary parametrisations of these arcs
  have hpar : ∀ n, ∃ γ : ℝ → C, Function.Injective γ ∧ IsLocalDiffeomorph 𝓘(ℝ) I1 sm γ ∧
      Set.range γ = A n := fun n => by
    obtain ⟨γ, h1, h2, h3⟩ := hc (A n) (hAc n)
    exact ⟨γ, h1, h2, h3.symm⟩
  choose par hpinj hpld hprng using hpar
  -- 3. countably many compact sets covering `U`: all windows of all these arcs
  let K : ℕ → Set C := fun k => par (Nat.unpair k).1 ''
    Set.Icc (-(((Nat.unpair k).2 : ℕ) : ℝ)) (((Nat.unpair k).2 : ℕ) : ℝ)
  have hKcomp : ∀ k, IsCompact (K k) := fun k =>
    isCompact_Icc.image (hpld _).contMDiff.continuous
  have hKsub : ∀ k, K k ⊆ ⋃₀ c := fun k => by
    refine (Set.image_subset_range _ _).trans ?_
    rw [hprng, ← hAcov]
    exact subset_iUnion A _
  have hKunion : ⋃ k, K k = ⋃₀ c := by
    apply le_antisymm
    · exact iUnion_subset hKsub
    · intro x hx
      rw [← hAcov] at hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      rw [← hprng n] at hn
      obtain ⟨t, rfl⟩ := hn
      refine mem_iUnion.mpr ⟨Nat.pair n ⌈|t|⌉₊, t, ⟨?_, ?_⟩, ?_⟩
      · rw [Nat.unpair_pair]; exact neg_le_of_abs_le (Nat.le_ceil |t|)
      · rw [Nat.unpair_pair]; exact le_of_abs_le (Nat.le_ceil |t|)
      · rw [Nat.unpair_pair]
  -- 4. pick indices so that `K n ⊆ A (σ n)`
  have hkA : ∀ k, ∃ m, K k ⊆ A m := by
    intro k
    obtain ⟨M, hMc, hKM⟩ := exists_mem_of_compact_subset_sUnion hco hchain hne (hKcomp k)
      (by rw [← hKunion]; exact subset_iUnion _ k)
    have hxU : ∀ x ∈ K k, x ∈ ⋃ m, A m := by
      intro x hx
      rw [hAcov]
      exact subset_sUnion_of_mem hMc (hKM hx)
    have hcover : K k ⊆ ⋃ m, A m ∩ M := by
      intro x hx
      obtain ⟨m, hxm⟩ := mem_iUnion.mp (hxU x hx)
      exact mem_iUnion.mpr ⟨m, hxm, hKM hx⟩
    obtain ⟨s, hs⟩ := (hKcomp k).elim_finite_subcover (fun m : ℕ => A m ∩ M)
      (fun m => (hco (A m) (hAc m)).inter (hco M hMc)) hcover
    refine ⟨s.sup id, fun x hx => ?_⟩
    obtain ⟨m, hms, hxAM⟩ := mem_iUnion₂.mp (hs hx)
    exact hAmono (Finset.le_sup (f := id) hms) hxAM.1
  let mOf : ℕ → ℕ := fun k => Classical.choose (hkA k)
  have hmOf : ∀ k, K k ⊆ A (mOf k) := fun k => Classical.choose_spec (hkA k)
  let σ : ℕ → ℕ := fun n =>
    Nat.rec (mOf 0) (fun k ih => max (max (ih + 1) (k + 1)) (mOf (k + 1))) n
  have hσsucc : ∀ n, σ (n+1) = max (max (σ n + 1) (n + 1)) (mOf (n+1)) := fun n => rfl
  have hσincr : ∀ n, σ n < σ (n+1) := by
    intro n
    rw [hσsucc]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hσmono : Monotone σ := monotone_nat_of_le_succ (fun n => le_of_lt (hσincr n))
  have hKσ : ∀ n, K n ⊆ A (σ n) := by
    intro n
    induction n with
    | zero => exact hmOf 0
    | succ n ih => rw [hσsucc]; exact (hmOf (n+1)).trans (hAmono (le_max_right _ _))
  -- 5. the recursive construction of compatible parametrisations with growing windows
  let St : ℕ → Type _ := fun n => {p : (ℝ → C) × ℝ // Function.Injective p.1 ∧
      IsLocalDiffeomorph 𝓘(ℝ) I1 sm p.1 ∧ Set.range p.1 = A (σ n) ∧ 0 ≤ p.2 ∧
      K n ⊆ p.1 '' Set.Icc (-p.2) p.2}
  have hbase_ex : ∃ p : (ℝ → C) × ℝ, Function.Injective p.1 ∧
      IsLocalDiffeomorph 𝓘(ℝ) I1 sm p.1 ∧ Set.range p.1 = A (σ 0) ∧ 0 ≤ p.2 ∧
      K 0 ⊆ p.1 '' Set.Icc (-p.2) p.2 := by
    obtain ⟨B, hB0, hKB⟩ := exists_Icc_of_compact_subset_range (hpld (σ 0)).isOpenMap (hKcomp 0)
      (by rw [hprng (σ 0)]; exact hKσ 0)
    refine ⟨(par (σ 0), |B| + 1), hpinj _, hpld _, hprng _, by positivity, ?_⟩
    have hBm : Set.Icc (-B) B ⊆ Set.Icc (-(|B| + 1)) (|B| + 1) := fun u hu =>
      ⟨by linarith [hu.1, le_abs_self B], by linarith [hu.2, le_abs_self B, abs_nonneg B]⟩
    exact hKB.trans (Set.image_mono hBm)
  let base : St 0 := ⟨Classical.choose hbase_ex, (Classical.choose_spec hbase_ex).1,
    (Classical.choose_spec hbase_ex).2.1, (Classical.choose_spec hbase_ex).2.2.1,
    (Classical.choose_spec hbase_ex).2.2.2.1, (Classical.choose_spec hbase_ex).2.2.2.2⟩
  have hstepE : ∀ n (s : St n), ∃ s' : St (n+1), s.1.2 + 1 ≤ s'.1.2 ∧
      Set.EqOn s'.1.1 s.1.1 (Set.Icc (-s.1.2) s.1.2) := by
    rintro n ⟨⟨γ, N⟩, hinjγ, hldγ, hrngγ, hN0, hKγ⟩
    have hsub : Set.range γ ⊆ A (σ (n+1)) := by
      rw [hrngγ]; exact hAmono (le_of_lt (hσincr n))
    obtain ⟨γ', hinj', hld', hrng', heq'⟩ :=
      arc_step_extend (hc (A (σ (n+1))) (hAc (σ (n+1)))) hinjγ hldγ hsub N
    obtain ⟨B, hB0, hKB⟩ := exists_Icc_of_compact_subset_range hld'.isOpenMap (hKcomp (n+1))
      (by rw [hrng']; exact hKσ (n+1))
    refine ⟨⟨(γ', |B| + N + 1), hinj', hld', hrng', by positivity, ?_⟩, ?_, heq'⟩
    · have hBm : Set.Icc (-B) B ⊆ Set.Icc (-(|B| + N + 1)) (|B| + N + 1) := fun u hu =>
        ⟨by linarith [hu.1, le_abs_self B, hN0],
         by linarith [hu.2, le_abs_self B, abs_nonneg B, hN0]⟩
      exact hKB.trans (Set.image_mono hBm)
    · linarith [abs_nonneg B]
  let step : ∀ n, St n → St (n+1) := fun n s => Classical.choose (hstepE n s)
  have step_mono : ∀ n (s : St n), s.1.2 + 1 ≤ (step n s).1.2 :=
    fun n s => (Classical.choose_spec (hstepE n s)).1
  have step_eq : ∀ n (s : St n), Set.EqOn (step n s).1.1 s.1.1 (Set.Icc (-s.1.2) s.1.2) :=
    fun n s => (Classical.choose_spec (hstepE n s)).2
  let seq : ∀ n, St n := fun n => Nat.rec (motive := St) base (fun k ih => step k ih) n
  have hseq_succ : ∀ n, seq (n+1) = step n (seq n) := fun n => rfl
  have hseq_inj : ∀ n, Function.Injective (seq n).1.1 := fun n => (seq n).2.1
  have hseq_rng : ∀ n, Set.range (seq n).1.1 = A (σ n) := fun n => (seq n).2.2.2.1
  have hseq_N0 : ∀ n, 0 ≤ (seq n).1.2 := fun n => (seq n).2.2.2.2.1
  have hseq_K : ∀ n, K n ⊆ (seq n).1.1 '' Set.Icc (-(seq n).1.2) (seq n).1.2 :=
    fun n => (seq n).2.2.2.2.2
  have hNstr : ∀ n, (seq n).1.2 + 1 ≤ (seq (n+1)).1.2 := by
    intro n; rw [hseq_succ n]; exact step_mono n (seq n)
  have hNge : ∀ n : ℕ, (n : ℝ) ≤ (seq n).1.2 := by
    intro n
    induction n with
    | zero => simpa using hseq_N0 0
    | succ n ih => exact le_trans (by push_cast; linarith) (hNstr n)
  have hNle : ∀ m n, m ≤ n → (seq m).1.2 ≤ (seq n).1.2 := by
    intro m n hmn
    induction n with
    | zero => rw [Nat.le_zero.mp hmn]
    | succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with h | h
      · exact (ih (Nat.lt_succ_iff.mp h)).trans (le_of_lt (lt_of_lt_of_le (by linarith) (hNstr n)))
      · rw [h]
  have hcompat : ∀ m n, m ≤ n → Set.EqOn (seq n).1.1 (seq m).1.1
      (Set.Icc (-(seq m).1.2) (seq m).1.2) := by
    intro m n hmn
    induction n with
    | zero => rw [Nat.le_zero.mp hmn]; exact fun _ _ => rfl
    | succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with h | h
      · have h1 : Set.EqOn (seq (n+1)).1.1 (seq n).1.1
            (Set.Icc (-(seq n).1.2) (seq n).1.2) := by
          rw [hseq_succ n]; exact step_eq n (seq n)
        have h2 : (seq m).1.2 ≤ (seq n).1.2 := hNle m n (Nat.lt_succ_iff.mp h)
        refine (h1.mono ?_).trans (ih (Nat.lt_succ_iff.mp h))
        intro t ht
        exact ⟨by linarith [ht.1, h2], by linarith [ht.2, h2]⟩
      · rw [h]; exact fun _ _ => rfl
  -- 6. glue
  have hNexists : ∀ t : ℝ, ∃ n, |t| ≤ (seq n).1.2 := fun t =>
    ⟨⌈|t|⌉₊, le_trans (Nat.le_ceil |t|) (hNge ⌈|t|⌉₊)⟩
  let mfun : ℝ → ℕ := fun t => Nat.find (hNexists t)
  have hmfun_abs : ∀ t : ℝ, |t| ≤ (seq (mfun t)).1.2 := fun t => Nat.find_spec (hNexists t)
  have hmfun_min' : ∀ t n, |t| ≤ (seq n).1.2 → mfun t ≤ n := fun t n hn =>
    Nat.find_min' (hNexists t) hn
  have hmfun : ∀ t : ℝ, t ∈ Set.Icc (-(seq (mfun t)).1.2) (seq (mfun t)).1.2 := fun t =>
    Set.mem_Icc.mpr ⟨neg_le_of_abs_le (hmfun_abs t), le_of_abs_le (hmfun_abs t)⟩
  let γ : ℝ → C := fun t => (seq (mfun t)).1.1 t
  have hγin : Function.Injective γ := by
    intro s t hst
    have hs : mfun s ≤ max (mfun s) (mfun t) := le_max_left _ _
    have ht : mfun t ≤ max (mfun s) (mfun t) := le_max_right _ _
    have h1 : (seq (mfun s)).1.1 s = (seq (max (mfun s) (mfun t))).1.1 s :=
      ((hcompat (mfun s) (max (mfun s) (mfun t)) hs) (hmfun s)).symm
    have h2 : (seq (mfun t)).1.1 t = (seq (max (mfun s) (mfun t))).1.1 t :=
      ((hcompat (mfun t) (max (mfun s) (mfun t)) ht) (hmfun t)).symm
    exact hseq_inj _ (by rw [← h1, ← h2]; exact hst)
  have hγld : IsLocalDiffeomorph 𝓘(ℝ) I1 sm γ := by
    intro t
    refine isLocalDiffeomorphAt_congr (((seq (mfun t + 1)).2.2.1) t) ?_
    have hstr : (seq (mfun t)).1.2 < (seq (mfun t + 1)).1.2 := by
      have := hNstr (mfun t); linarith
    have hmem : Set.Ioo (-(seq (mfun t + 1)).1.2) (seq (mfun t + 1)).1.2 ∈ 𝓝 t := by
      refine Ioo_mem_nhds ?_ ?_
      · linarith [(hmfun t).1, hstr]
      · linarith [(hmfun t).2, hstr]
    refine Filter.eventuallyEq_of_mem hmem ?_
    intro u hu
    have hu' : |u| ≤ (seq (mfun t + 1)).1.2 := le_of_lt (abs_lt.mpr ⟨hu.1, hu.2⟩)
    have h1 : mfun u ≤ mfun t + 1 := hmfun_min' u _ hu'
    exact (hcompat (mfun u) (mfun t + 1) h1) (hmfun u)
  refine ⟨γ, hγin, hγld, ?_⟩
  apply le_antisymm
  · rw [← hKunion]
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    obtain ⟨u, hu, rfl⟩ := hseq_K k hk
    have h1 : mfun u ≤ k := hmfun_min' u k (by
      rw [abs_le]; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    refine ⟨u, ?_⟩
    show (seq (mfun u)).1.1 u = (seq k).1.1 u
    exact ((hcompat (mfun u) k h1) (hmfun u)).symm
  · intro x hx
    obtain ⟨t, rfl⟩ := hx
    rw [← hAcov]
    exact mem_iUnion.mpr ⟨σ (mfun t), by rw [← hseq_rng (mfun t)]; exact Set.mem_range_self t⟩

end Work.OneDim
