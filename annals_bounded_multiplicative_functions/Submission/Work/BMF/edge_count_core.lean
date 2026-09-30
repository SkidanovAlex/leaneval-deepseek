import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Counting core: if `Im` indexes a family with values `f` bounded above by
`Fmax`, if `Im` has at most `Emax` elements, and if `N` is at most the total mass
`∑ f`, then at least `N / (2 Fmax)` members carry value `≥ N / (2 Emax)`.

This is the standard "large values" counting fact: the sub-level set `T` has mass
`≤ |T| · N / (2 Emax) ≤ N / 2`, so the complement `S` carries mass `≥ N / 2`,
which forces `|S| · Fmax ≥ N / 2`. -/
lemma card_filter_ge_aux {E : Type*} [DecidableEq E]
    (Im : Finset E) (f : E → ℝ) (N Emax Fmax : ℝ)
    (hN0 : 0 ≤ N) (hEmax : 0 < Emax) (hFmax : 0 < Fmax)
    (hIm : (Im.card : ℝ) ≤ Emax)
    (hfmax : ∀ e ∈ Im, f e ≤ Fmax)
    (hN : N ≤ ∑ e ∈ Im, f e) :
    N / (2 * Fmax) ≤ ((Im.filter (fun e => N / (2 * Emax) ≤ f e)).card : ℝ) := by
  classical
  set S := Im.filter (fun e => N / (2 * Emax) ≤ f e) with hS
  set T := Im.filter (fun e => ¬ (N / (2 * Emax) ≤ f e)) with hT
  have hpart : S.sum f + T.sum f = Im.sum f := by
    rw [hS, hT]
    exact Finset.sum_filter_add_sum_filter_not Im (fun e => N / (2 * Emax) ≤ f e) f
  have hSsub : S ⊆ Im := by rw [hS]; exact Finset.filter_subset _ _
  have hTsub : T ⊆ Im := by rw [hT]; exact Finset.filter_subset _ _
  -- mass of `S` is at most `|S| · Fmax`
  have hSle : S.sum f ≤ (S.card : ℝ) * Fmax := by
    calc S.sum f ≤ S.card • Fmax :=
          Finset.sum_le_card_nsmul S f Fmax (fun e he => hfmax e (hSsub he))
      _ = (S.card : ℝ) * Fmax := by rw [nsmul_eq_mul]
  -- mass of `T` is at most `|T| · N / (2 Emax)`
  have hTle : T.sum f ≤ (T.card : ℝ) * (N / (2 * Emax)) := by
    calc T.sum f ≤ T.card • (N / (2 * Emax)) :=
          Finset.sum_le_card_nsmul T f (N / (2 * Emax)) (fun e he => by
            rw [hT] at he
            have hne : ¬ (N / (2 * Emax) ≤ f e) := (Finset.mem_filter.mp he).2
            exact le_of_lt (not_le.mp hne))
      _ = (T.card : ℝ) * (N / (2 * Emax)) := by rw [nsmul_eq_mul]
  have hTcard : (T.card : ℝ) ≤ Emax := by
    have h1 : T.card ≤ Im.card := Finset.card_le_card hTsub
    have h2 : (T.card : ℝ) ≤ (Im.card : ℝ) := by exact_mod_cast h1
    linarith
  have hEmul : Emax * (N / (2 * Emax)) = N / 2 := by
    field_simp
  have hnonneg : 0 ≤ N / (2 * Emax) := div_nonneg hN0 (by positivity)
  have hmul : (T.card : ℝ) * (N / (2 * Emax)) ≤ N / 2 := by
    rw [← hEmul]
    exact mul_le_mul_of_nonneg_right hTcard hnonneg
  have hN2 : N / 2 ≤ (S.card : ℝ) * Fmax := by
    have h1 : N ≤ (S.card : ℝ) * Fmax + N / 2 := by
      calc N ≤ Im.sum f := hN
        _ = S.sum f + T.sum f := hpart.symm
        _ ≤ (S.card : ℝ) * Fmax + N / 2 := by linarith
    linarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Fmax)]
  nlinarith [hN2]

/-- Counting core for the "edges in a bipartite graph" argument.

`DOM` is a finite set of "edges" `((k,p),(p',p''))`; `ed` labels them in `E`.
The hypothesis `hinj` says that within a fibre of `ed` the map `q ↦ q.1.2` is
injective (distinct `p`-coordinates), hence each fibre has as many elements as it
has distinct `p`-coordinates.  With the set of labels of size `≤ Emax` and each
fibre of size `≤ Fmax`, at least `|DOM| / (2 Fmax)` labels `e` carry at least
`|DOM| / (2 Emax)` distinct `p`-coordinates. -/
theorem edge_count_core {K P P' E : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq P'] [DecidableEq E]
    (KF : Finset (K × P)) (G : K × P → Finset P') (DOM : Finset ((K × P) × (P' × P')))
    (ed : (K × P) × (P' × P') → E)
    (hinj : ∀ q ∈ DOM, ∀ q' ∈ DOM, ed q = ed q' → q.1.2 = q'.1.2 → q = q')
    (Q Kbd Emax Fmax : ℝ) (hQ : 0 < Q) (hKbd : 0 < Kbd) (hEmax : 0 < Emax) (hFmax : 0 < Fmax)
    (hKF : (KF.card : ℝ) ≤ Kbd)
    (hcard : Q ^ 2 / Kbd - Q ≤ (DOM.card : ℝ))
    (hE : ((DOM.image ed).card : ℝ) ≤ Emax)
    (hfib : ∀ e : E, ((DOM.filter (fun q => ed q = e)).card : ℝ) ≤ Fmax) :
    ∃ A : Finset E, (DOM.card : ℝ) / (2 * Fmax) ≤ (A.card : ℝ) ∧
      ∀ e ∈ A, ∃ S : Finset P, (∀ p ∈ S, ∃ q ∈ DOM, ed q = e ∧ q.1.2 = p) ∧
        (DOM.card : ℝ) / (2 * Emax) ≤ (S.card : ℝ) := by
  classical
  set f : E → ℝ := fun e => ((DOM.filter (fun q => ed q = e)).card : ℝ) with hf
  set Im : Finset E := DOM.image ed with hIm
  set N : ℝ := (DOM.card : ℝ) with hN
  -- The fibres of `ed` over its image partition `DOM`.
  have hsumNat : DOM.card = ∑ e ∈ Im, (DOM.filter (fun q => ed q = e)).card := by
    rw [hIm]
    exact Finset.card_eq_sum_card_fiberwise (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  have hsum : N = ∑ e ∈ Im, f e := by
    rw [hN, hf, hsumNat]
    push_cast
    rfl
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  have hImcard : (Im.card : ℝ) ≤ Emax := by rw [hIm]; exact hE
  have hfmaxIm : ∀ e ∈ Im, f e ≤ Fmax := by
    intro e _
    rw [hf]
    exact hfib e
  -- Many labels carry a large fibre.
  have hcount := card_filter_ge_aux Im f N Emax Fmax hN0 hEmax hFmax hImcard hfmaxIm (le_of_eq hsum)
  refine ⟨Im.filter (fun e => N / (2 * Emax) ≤ f e), hcount, ?_⟩
  intro e he
  -- `hinj` makes each fibre inject into its set of `p`-coordinates.
  have hef : N / (2 * Emax) ≤ f e := (Finset.mem_filter.mp he).2
  refine ⟨(DOM.filter (fun q => ed q = e)).image (fun q => q.1.2), ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    exact ⟨q, (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2, hpq⟩
  · rw [Finset.card_image_of_injOn]
    · rw [hf] at hef
      exact hef
    · intro q hq q' hq' hqeq
      exact hinj q (Finset.mem_filter.mp hq).1 q' (Finset.mem_filter.mp hq').1
        (by rw [(Finset.mem_filter.mp hq).2, (Finset.mem_filter.mp hq').2]) hqeq

end Work.BMF
