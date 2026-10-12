import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# `Submission.Work.BoseFixB1S.boxPairValue`

The collapsing identity of the two-body (pair) line at the FS-faithful box projections
`boxPInd (boxMass ℓ d u) (dlBox ℓ d u)`:

`Σ_{p ∈ pairSet n} ∫_{abox n ℓ} (P_{B,p₁}P_{B,p₂}Φ)² f(x_{p₁},x_{p₂})
  = (|B|²)⁻¹ (∬_{B×B} f) Σ_{p ∈ pairSet n} ∫_{abox n ℓ} (P_{B,p₁}P_{B,p₂}Φ)²`,

`B = B(u) = dlBox ℓ d u`, `|B| = boxMass ℓ d u`.

The proof is *junk-tolerant*: no measurability/integrability hypothesis on `Φ`, `f`
(only the uses the closing `Σ_p ∫(...)²` term, the same one on both sides).  The two
tools are

* `MeasurePreserving.integral_comp` (with a `MeasurableEmbedding`) — the two-slot peel
  of the centred box, valid for an *arbitrary* integrand (`abox_peel2`), and
* `integral_prod_mul` — the product factorization of a two-variable integrand which,
  unlike Fubini, also holds for non-integrable functions (it is stated for arbitrary
  `f, g` in Mathlib).

The pointwise content is that the double box projection factors as
`P_{B,i}P_{B,j}Φ x = |B|⁻² 1_B(x_i) 1_B(x_j) K(x)` with `K` depending only on the
coordinates outside `{i,j}`; both sides of the identity are then the *same* product
`(∬_{B×B}f) · (∫ K_r²)` up to the constant `|B|²`.
-/

/-! ## 1. Elementary helpers -/

/-- The pair set is empty in the degenerate cases `n ≤ 1`.

Hygiene fix (this session): made `private` — `Work.BoseFixB1S.boxPQw_mass_le.lean:71` declares
the *same* name non-privately, and any import cone containing both files previously failed with
"a non-private declaration has already been declared" (this blocked the assembly of
`FINDING_mfSection10FewB1_session3.md` §10).  This copy is used only in this file (lines 408/410). -/
private lemma pairSet_eq_empty_of_le_one {n : ℕ} (hn : n ≤ 1) : pairSet n = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  rw [pairSet, Finset.mem_filter] at hp
  refine hp.2 (Fin.ext ?_)
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  omega

/-- The box mass is the integral of the box indicator against the cube-restricted volume. -/
lemma boxMass_eq_setIntegral {ℓ d : ℝ} (u : kcE3) :
    (∫ x : kcE3, (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) x
        ∂((volume : Measure kcE3).restrict (acube ℓ)))
      = Work.SmallBoxSliding.boxMass ℓ d u := by
  have hAc : dlBox ℓ d u ⊆ acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hind : (fun x : kcE3 => (acube ℓ).indicator
        ((dlBox ℓ d u).indicator (fun _ => (1 : ℝ))) x)
      = (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ acube ℓ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      by_cases hx2 : x ∈ dlBox ℓ d u
      · exact absurd (hAc hx2) hx
      · rw [Set.indicator_of_notMem hx2]
  rw [← integral_indicator (acube_measurable ℓ), hind]
  rfl

/-- The indicator of the box takes the values `0` and `1`, hence is idempotent. -/
lemma ind_sq {ℓ d : ℝ} (u : kcE3) (y : kcE3) :
    ((dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y) ^ 2
      = (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y := by
  by_cases h : y ∈ dlBox ℓ d u
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num

/-- The scalar collapsing step: `((1/V)²AB C)² G = (1/V)⁴ ((ABG)C²)` for idempotent `A`, `B`. -/
lemma pair_int_factor (V A B C G : ℝ) (hA : A ^ 2 = A) (hB : B ^ 2 = B) :
    ((1 / V) ^ 2 * A * B * C) ^ 2 * G = (1 / V) ^ 4 * ((A * B * G) * C ^ 2) := by
  have h1 : ((1 / V) ^ 2 * A * B * C) ^ 2 = (1 / V) ^ 4 * A * B * C ^ 2 := by
    calc ((1 / V) ^ 2 * A * B * C) ^ 2
        = (1 / V) ^ 4 * A ^ 2 * B ^ 2 * C ^ 2 := by ring
      _ = (1 / V) ^ 4 * A * B * C ^ 2 := by rw [hA, hB]
  rw [h1]
  ring

/-! ## 2. The two-slot peel of the centred box -/

/-- Function-level `update` congruence: two configurations agreeing off the two slots
`i`, `j` give the same double update. -/
lemma update_update_eq_of_agree {N : ℕ} {i j : Fin N} (hij : i ≠ j) {x x' : X N}
    (h : ∀ k, k ≠ i → k ≠ j → x k = x' k) (z w : kcE3) :
    Function.update (Function.update x i z) j w
      = Function.update (Function.update x' i z) j w := by
  funext k
  by_cases hkj : k = j
  · subst hkj
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
    by_cases hki : k = i
    · subst hki
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hki, Function.update_of_ne hki]
      exact h k hki hkj

/-- The restricted two-slot kernel depends only on the slots outside `{i, i.succAbove j'}`. -/
lemma pairK_off_const {m : ℕ} {ℓ d : ℝ} (u : kcE3) (Φ : X (m + 2) → ℝ)
    {i : Fin (m + 2)} {j' : Fin (m + 1)} {x x' : X (m + 2)}
    (h : ∀ k, k ≠ i → k ≠ i.succAbove j' → x k = x' k) :
    (∫ z in dlBox ℓ d u, ∫ w in dlBox ℓ d u,
        Φ (Function.update (Function.update x i z) (i.succAbove j') w))
      = (∫ z in dlBox ℓ d u, ∫ w in dlBox ℓ d u,
        Φ (Function.update (Function.update x' i z) (i.succAbove j') w)) := by
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards with w
  exact congrArg Φ (update_update_eq_of_agree
    (i := i) (j := i.succAbove j') (Fin.succAbove_ne i j').symm h z w)

/-- The double insertion `ins2` is insensitive to the inserted values in the slots
outside `{i, i.succAbove j'}`. -/
lemma ins2_eq_rest2_of_ne {m : ℕ} (i : Fin (m + 2)) (j' : Fin (m + 1)) (y z : kcE3)
    (r : X m) {k : Fin (m + 2)} (hki : k ≠ i) (hkj : k ≠ i.succAbove j') :
    ins2 i j' y z r k = rest2 i j' r k := by
  rcases Fin.exists_succAbove_eq (x := k) (y := i) hki with ⟨l, hl⟩
  rw [← hl]
  have h1 : ins2 i j' y z r (i.succAbove l) = (kcInsN m j' (z, r)) l := by
    dsimp only [ins2]
    exact kc_insN_apply_succ (m + 1) i y (kcInsN m j' (z, r)) l
  have h2 : rest2 i j' r (i.succAbove l) = (kcInsN m j' (0, r)) l := by
    dsimp only [rest2, ins2]
    exact kc_insN_apply_succ (m + 1) i 0 (kcInsN m j' (0, r)) l
  rw [h1, h2]
  have hlne : l ≠ j' := by
    intro hlj
    exact hkj (by rw [← hl, hlj])
  rcases Fin.exists_succAbove_eq (x := l) (y := j') hlne with ⟨n, hn⟩
  have h3 : (kcInsN m j' (z, r)) l = r n := by
    rw [← hn]
    exact kc_insN_apply_succ m j' z r n
  have h4 : (kcInsN m j' (0, r)) l = r n := by
    rw [← hn]
    exact kc_insN_apply_succ m j' 0 r n
  rw [h3, h4]

/-- **The two-slot peel of the centred box, junk-tolerant form**: for an *arbitrary*
integrand `F` the box integral is the integral over the two isolated slots and the rest,
against the product of the restricted measures.  (No measurability or integrability.) -/
lemma abox_peel2 {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (m + 2)) (j' : Fin (m + 1))
    (F : X (m + 2) → ℝ) :
    (∫ x in abox (m + 2) ℓ, F x)
      = ∫ q : (kcE3 × kcE3) × X m, F (ins2 i j' q.1.1 q.1.2 q.2)
          ∂(((((volume : Measure kcE3).restrict (acube ℓ)).prod
              ((volume : Measure kcE3).restrict (acube ℓ))).prod
            ((volume : Measure (X m)).restrict (abox m ℓ)))) := by
  have h1 : MeasurePreserving (fun q : (kcE3 × kcE3) × X m =>
      kcInsN (m + 1) i (q.1.1, kcInsN m j' (q.1.2, q.2)))
      ((((volume : Measure kcE3).restrict (acube ℓ)).prod
          ((volume : Measure kcE3).restrict (acube ℓ))).prod
        ((volume : Measure (X m)).restrict (abox m ℓ)))
      ((volume : Measure (X (m + 2))).restrict (abox (m + 2) ℓ)) :=
    ins2_flat_mp (p := m) hℓ i j'
  have h2 : MeasurableEmbedding (fun q : (kcE3 × kcE3) × X m =>
      kcInsN (m + 1) i (q.1.1, kcInsN m j' (q.1.2, q.2))) := by
    have hfun : (fun q : (kcE3 × kcE3) × X m =>
        kcInsN (m + 1) i (q.1.1, kcInsN m j' (q.1.2, q.2)))
        = (⇑(kcInsN (m + 1) i)) ∘ (Prod.map id (⇑(kcInsN m j')))
            ∘ ⇑(MeasurableEquiv.prodAssoc) := by
      funext q
      rcases q with ⟨⟨y, z⟩, r⟩
      rfl
    rw [hfun]
    exact ((MeasurableEquiv.measurableEmbedding (kcInsN (m + 1) i)).comp
      ((MeasurableEmbedding.prodMap MeasurableEmbedding.id
          (MeasurableEquiv.measurableEmbedding (kcInsN m j'))).comp
        (MeasurableEquiv.measurableEmbedding MeasurableEquiv.prodAssoc)))
  exact (h1.integral_comp h2 F).symm

/-! ## 3. The two-slot mass functionals -/

/-- The `(B × B)`-mass of a pair kernel on the two-slot fibre. -/
noncomputable def pairMass (ℓ d : ℝ) (u : kcE3) (g : kcE3 → kcE3 → ℝ) : ℝ :=
  ∫ y : kcE3 × kcE3, (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y.1
      * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y.2 * g y.1 y.2
    ∂(((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure kcE3).restrict (acube ℓ)))

/-- The restricted two-slot kernel of the double box projection, as a function of the
coordinates outside the two slots. -/
noncomputable def pairKernel {m : ℕ} (ℓ d : ℝ) (u : kcE3) (i : Fin (m + 2))
    (j' : Fin (m + 1)) (Φ : X (m + 2) → ℝ) (r : X m) : ℝ :=
  ∫ z in dlBox ℓ d u, ∫ w in dlBox ℓ d u,
    Φ (Function.update (Function.update (rest2 i j' r) i z) (i.succAbove j') w)

/-- `pairMass` is the set integral of the kernel over `B × B`. -/
lemma pairMass_eq_setIntegral {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : kcE3) (g : kcE3 → kcE3 → ℝ) :
    pairMass ℓ d u g
      = ∫ q in dlBox ℓ d u ×ˢ dlBox ℓ d u, g q.1 q.2 := by
  have hAmeas : MeasurableSet (dlBox ℓ d u) := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : dlBox ℓ d u ⊆ acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hpt : ∀ y : kcE3 × kcE3, (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y.1
        * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y.2 * g y.1 y.2
      = (dlBox ℓ d u ×ˢ dlBox ℓ d u).indicator (fun y => g y.1 y.2) y := by
    intro y
    by_cases hy : y ∈ dlBox ℓ d u ×ˢ dlBox ℓ d u
    · have h1 : y.1 ∈ dlBox ℓ d u := (Set.mem_prod.mp hy).1
      have h2 : y.2 ∈ dlBox ℓ d u := (Set.mem_prod.mp hy).2
      rw [Set.indicator_of_mem (s := dlBox ℓ d u ×ˢ dlBox ℓ d u) hy,
        Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      simp
    · rw [Set.indicator_of_notMem (s := dlBox ℓ d u ×ˢ dlBox ℓ d u) hy]
      have h : ¬(y.1 ∈ dlBox ℓ d u ∧ y.2 ∈ dlBox ℓ d u) := fun hcon =>
        hy (Set.mem_prod.mpr hcon)
      rcases not_and_or.mp h with h1 | h2
      · rw [Set.indicator_of_notMem h1, zero_mul, zero_mul]
      · rw [Set.indicator_of_notMem h2, mul_zero, zero_mul]
  have hmeas : ((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure kcE3).restrict (acube ℓ))
      = (volume : Measure (kcE3 × kcE3)).restrict (acube ℓ ×ˢ acube ℓ) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod kcE3 kcE3]
  simp only [pairMass]
  rw [show (fun y : kcE3 × kcE3 => (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y.1
        * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y.2 * g y.1 y.2)
      = (dlBox ℓ d u ×ˢ dlBox ℓ d u).indicator (fun y => g y.1 y.2)
      from funext hpt]
  rw [hmeas]
  rw [integral_indicator (hAmeas.prod hAmeas)]
  rw [Measure.restrict_restrict (hAmeas.prod hAmeas)]
  rw [Set.inter_eq_self_of_subset_left (Set.prod_mono hAc hAc)]

/-- The pair mass of the constant kernel `1` is the square of the box mass. -/
lemma pairMass_one {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : kcE3) :
    pairMass ℓ d u (fun _ _ => (1 : ℝ))
      = Work.SmallBoxSliding.boxMass ℓ d u * Work.SmallBoxSliding.boxMass ℓ d u := by
  have hpt : (fun y : kcE3 × kcE3 => (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y.1
        * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y.2
        * (fun _ _ => (1 : ℝ)) y.1 y.2)
      = (fun y : kcE3 × kcE3 => (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y.1
        * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y.2) := by
    funext y
    simp
  simp only [pairMass]
  rw [hpt]
  rw [integral_prod_mul
    (f := fun y : kcE3 => (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y)
    (g := fun y : kcE3 => (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y)]
  rw [boxMass_eq_setIntegral]

/-! ## 4. The per-pair collapsing identity -/

/-- **The per-pair collapse**: at a fixed ordered pair `(i, i.succAbove j')` of slots, the
weighted pair integral collapses onto the product of the `B × B`-mass and the two-slot
kernel integral. -/
lemma pairValue_int {m : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : kcE3) {Φ : X (m + 2) → ℝ}
    {i : Fin (m + 2)} {j' : Fin (m + 1)} (g : kcE3 → kcE3 → ℝ) :
    (∫ x in abox (m + 2) ℓ,
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
            (i.succAbove j') Φ) x) ^ 2 * g (x i) (x (i.succAbove j')))
      = (1 / Work.SmallBoxSliding.boxMass ℓ d u) ^ 4 * pairMass ℓ d u g
          * (∫ r : X m, (pairKernel ℓ d u i j' Φ r) ^ 2
              ∂((volume : Measure (X m)).restrict (abox m ℓ))) := by
  have hfac : ∀ x : X (m + 2),
      (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
          (i.succAbove j') Φ) x)
        = (1 / Work.SmallBoxSliding.boxMass ℓ d u) ^ 2
            * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
            * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x (i.succAbove j'))
            * (∫ z in dlBox ℓ d u, ∫ w in dlBox ℓ d u,
                Φ (Function.update (Function.update x i z) (i.succAbove j') w)) := by
    intro x
    simp only [Work.UBBInputs8.boxPInd]
    have hz : (∫ z in dlBox ℓ d u,
          (1 / Work.SmallBoxSliding.boxMass ℓ d u)
            * (∫ w in dlBox ℓ d u,
                Φ (Function.update (Function.update x i z) (i.succAbove j') w))
            * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ))
                ((Function.update x i z) (i.succAbove j')))
        = ((1 / Work.SmallBoxSliding.boxMass ℓ d u)
            * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x (i.succAbove j')))
          * (∫ z in dlBox ℓ d u, ∫ w in dlBox ℓ d u,
              Φ (Function.update (Function.update x i z) (i.succAbove j') w)) := by
      trans (∫ z in dlBox ℓ d u,
          ((1 / Work.SmallBoxSliding.boxMass ℓ d u)
              * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x (i.succAbove j')))
            * (∫ w in dlBox ℓ d u,
                Φ (Function.update (Function.update x i z) (i.succAbove j') w)))
      · apply integral_congr_ae
        filter_upwards with z
        rw [show (Function.update x i z) (i.succAbove j') = x (i.succAbove j') from
          Function.update_of_ne (Fin.succAbove_ne i j') z x]
        ring
      · rw [integral_const_mul]
    rw [hz]
    ring
  have hint : ∀ x : X (m + 2),
      (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
            (i.succAbove j') Φ) x) ^ 2 * g (x i) (x (i.succAbove j'))
        = (1 / Work.SmallBoxSliding.boxMass ℓ d u) ^ 4
            * (((dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
                  * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x (i.succAbove j'))
                  * g (x i) (x (i.succAbove j')))
                * (∫ z in dlBox ℓ d u, ∫ w in dlBox ℓ d u,
                    Φ (Function.update (Function.update x i z) (i.succAbove j') w)) ^ 2) := by
    intro x
    rw [hfac x]
    exact pair_int_factor _ _ _ _ _ (ind_sq u (x i)) (ind_sq u (x (i.succAbove j')))
  have hKc : ∀ (y z : kcE3) (r : X m),
      (∫ z' in dlBox ℓ d u, ∫ w in dlBox ℓ d u,
          Φ (Function.update (Function.update (ins2 i j' y z r) i z') (i.succAbove j') w))
        = pairKernel ℓ d u i j' Φ r := by
    intro y z r
    dsimp only [pairKernel]
    exact pairK_off_const u Φ (fun k hki hkj => ins2_eq_rest2_of_ne i j' y z r hki hkj)
  calc (∫ x in abox (m + 2) ℓ,
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) i
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
            (i.succAbove j') Φ) x) ^ 2 * g (x i) (x (i.succAbove j')))
      = ∫ x in abox (m + 2) ℓ, (1 / Work.SmallBoxSliding.boxMass ℓ d u) ^ 4
            * (((dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
                  * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x (i.succAbove j'))
                  * g (x i) (x (i.succAbove j')))
                * (∫ z in dlBox ℓ d u, ∫ w in dlBox ℓ d u,
                    Φ (Function.update (Function.update x i z) (i.succAbove j') w)) ^ 2) := by
        apply integral_congr_ae
        filter_upwards with x
        exact hint x
      _ = (1 / Work.SmallBoxSliding.boxMass ℓ d u) ^ 4
            * ∫ x in abox (m + 2) ℓ,
                (((dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
                    * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x (i.succAbove j'))
                    * g (x i) (x (i.succAbove j')))
                  * (∫ z in dlBox ℓ d u, ∫ w in dlBox ℓ d u,
                      Φ (Function.update (Function.update x i z) (i.succAbove j') w)) ^ 2) := by
        rw [integral_const_mul]
      _ = (1 / Work.SmallBoxSliding.boxMass ℓ d u) ^ 4
            * ∫ q : (kcE3 × kcE3) × X m,
                (((dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) q.1.1
                    * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) q.1.2
                    * g q.1.1 q.1.2)
                  * (pairKernel ℓ d u i j' Φ q.2) ^ 2)
              ∂(((volume : Measure kcE3).restrict (acube ℓ)).prod
                  ((volume : Measure kcE3).restrict (acube ℓ))).prod
                ((volume : Measure (X m)).restrict (abox m ℓ)) := by
        rw [abox_peel2 (m := m) hℓ i j' (fun x : X (m + 2) =>
            (((dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
                * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x (i.succAbove j'))
                * g (x i) (x (i.succAbove j')))
              * (∫ z in dlBox ℓ d u, ∫ w in dlBox ℓ d u,
                  Φ (Function.update (Function.update x i z) (i.succAbove j') w)) ^ 2))]
        congr 1
        apply integral_congr_ae
        filter_upwards with q
        have hq : (∫ z in dlBox ℓ d u, ∫ w in dlBox ℓ d u,
              Φ (Function.update (Function.update (ins2 i j' q.1.1 q.1.2 q.2) i z)
                (i.succAbove j') w)) = pairKernel ℓ d u i j' Φ q.2 := hKc q.1.1 q.1.2 q.2
        rw [ins2_apply_i, ins2_apply_succ, hq]
      _ = (1 / Work.SmallBoxSliding.boxMass ℓ d u) ^ 4
            * (pairMass ℓ d u g
                * (∫ r : X m, (pairKernel ℓ d u i j' Φ r) ^ 2
                    ∂((volume : Measure (X m)).restrict (abox m ℓ)))) := by
        rw [integral_prod_mul
          (f := fun y : kcE3 × kcE3 => (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y.1
              * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y.2 * g y.1 y.2)
          (g := fun r : X m => (pairKernel ℓ d u i j' Φ r) ^ 2)]
        simp only [pairMass]
      _ = (1 / Work.SmallBoxSliding.boxMass ℓ d u) ^ 4 * pairMass ℓ d u g
            * (∫ r : X m, (pairKernel ℓ d u i j' Φ r) ^ 2
                ∂((volume : Measure (X m)).restrict (abox m ℓ))) := by
        ring

/-! ## 5. The box pair identity -/

theorem boxPairValue {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ)
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (u : EuclideanSpace ℝ (Fin 3)) (Φ : Submission.BoseGases.X n → ℝ)
    (hf : MeasureTheory.IntegrableOn
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => f q.1 q.2)
      (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u)
      MeasureTheory.volume) :
    (∑ p ∈ Submission.BoseGases.pairSet n,
        ∫ x in Submission.BoseGases.abox n ℓ,
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) p.1
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2 * f (x p.1) (x p.2))
      = ((Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)⁻¹
          * (∫ q in Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u,
              f q.1 q.2)
          * (∑ p ∈ Submission.BoseGases.pairSet n,
              ∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1
                  (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2) := by
  classical
  rcases n with _ | _ | m
  · rw [pairSet_eq_empty_of_le_one (Nat.zero_le 1)]
    simp
  · rw [pairSet_eq_empty_of_le_one (le_refl 1)]
    simp
  · by_cases hV0 : Work.SmallBoxSliding.boxMass ℓ d u = 0
    · have hLHS : (∑ p ∈ pairSet (m + 2), ∫ x in abox (m + 2) ℓ,
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
                p.2 Φ) x) ^ 2 * f (x p.1) (x p.2)) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        have h1 : Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
            p.2 Φ = fun _ => (0 : ℝ) := by
          funext y
          simp [Work.UBBInputs8.boxPInd, hV0]
        rw [show (fun x : X (m + 2) =>
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) p.1
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
                  p.2 Φ) x) ^ 2 * f (x p.1) (x p.2)) = fun _ => (0 : ℝ) from by
            funext x
            rw [h1]
            simp [Work.UBBInputs8.boxPInd]]
        simp
      rw [hLHS]
      have hR : ((Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)⁻¹
            * (∫ q in dlBox ℓ d u ×ˢ dlBox ℓ d u, f q.1 q.2)
            * (∑ p ∈ pairSet (m + 2), ∫ x in abox (m + 2) ℓ,
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
                  p.1
                  (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
                    p.2 Φ) x) ^ 2) = 0 := by
        rw [hV0]
        simp
      rw [hR]
    · have hMf : pairMass ℓ d u f = ∫ q in dlBox ℓ d u ×ˢ dlBox ℓ d u, f q.1 q.2 :=
        pairMass_eq_setIntegral hℓ u f
      have hM1 : pairMass ℓ d u (fun _ _ => (1 : ℝ))
          = Work.SmallBoxSliding.boxMass ℓ d u * Work.SmallBoxSliding.boxMass ℓ d u :=
        pairMass_one hℓ u
      have hper : ∀ p ∈ pairSet (m + 2),
          (∫ x in abox (m + 2) ℓ,
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) p.1
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
                  p.2 Φ) x) ^ 2 * f (x p.1) (x p.2))
            = ((Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)⁻¹
                * (∫ q in dlBox ℓ d u ×ˢ dlBox ℓ d u, f q.1 q.2)
                * (∫ x in abox (m + 2) ℓ,
                    (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (dlBox ℓ d u) p.1
                      (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                        (dlBox ℓ d u) p.2 Φ) x) ^ 2) := by
        intro p hp
        obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (Finset.mem_filter.mp hp).2.symm
        rw [← hj']
        have hV2b : (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2 ≠ 0 := pow_ne_zero 2 hV0
        have h1 := pairValue_int (m := m) (ℓ := ℓ) (d := d) hℓ u (Φ := Φ)
          (i := p.1) (j' := j') (g := f)
        have h2 := pairValue_int (m := m) (ℓ := ℓ) (d := d) hℓ u (Φ := Φ)
          (i := p.1) (j' := j') (g := fun _ _ => (1 : ℝ))
        have h2' : (∫ x in abox (m + 2) ℓ,
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
                p.1
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
                  (p.1.succAbove j') Φ) x) ^ 2)
            = (1 / Work.SmallBoxSliding.boxMass ℓ d u) ^ 4
                * pairMass ℓ d u (fun _ _ => (1 : ℝ))
                * (∫ r : X m, (pairKernel ℓ d u p.1 j' Φ r) ^ 2
                    ∂((volume : Measure (X m)).restrict (abox m ℓ))) := by
          simpa only [mul_one] using h2
        have key : (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2
              * (∫ x in abox (m + 2) ℓ,
                  (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
                    p.1
                    (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
                      (p.1.succAbove j') Φ) x) ^ 2 * f (x p.1) (x (p.1.succAbove j')))
            = (∫ q in dlBox ℓ d u ×ˢ dlBox ℓ d u, f q.1 q.2)
              * (∫ x in abox (m + 2) ℓ,
                  (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
                    p.1
                    (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
                      (p.1.succAbove j') Φ) x) ^ 2) := by
          rw [h1, h2', hMf, hM1]
          ring
        calc (∫ x in abox (m + 2) ℓ,
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u) p.1
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) (dlBox ℓ d u)
                  (p.1.succAbove j') Φ) x) ^ 2 * f (x p.1) (x (p.1.succAbove j')))
            = (((Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)⁻¹
                * (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
                * (∫ x in abox (m + 2) ℓ,
                    (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (dlBox ℓ d u) p.1
                      (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                        (dlBox ℓ d u) (p.1.succAbove j') Φ) x) ^ 2
                      * f (x p.1) (x (p.1.succAbove j'))) := by
              rw [inv_mul_cancel₀ hV2b, one_mul]
          _ = ((Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)⁻¹
                * ((Work.SmallBoxSliding.boxMass ℓ d u) ^ 2
                    * (∫ x in abox (m + 2) ℓ,
                        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                          (dlBox ℓ d u) p.1
                          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                            (dlBox ℓ d u) (p.1.succAbove j') Φ) x) ^ 2
                          * f (x p.1) (x (p.1.succAbove j')))) := by
              ring
          _ = ((Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)⁻¹
                * ((∫ q in dlBox ℓ d u ×ˢ dlBox ℓ d u, f q.1 q.2)
                    * (∫ x in abox (m + 2) ℓ,
                        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                          (dlBox ℓ d u) p.1
                          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                            (dlBox ℓ d u) (p.1.succAbove j') Φ) x) ^ 2)) := by
              rw [key]
          _ = ((Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)⁻¹
                * (∫ q in dlBox ℓ d u ×ˢ dlBox ℓ d u, f q.1 q.2)
                * (∫ x in abox (m + 2) ℓ,
                    (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (dlBox ℓ d u) p.1
                      (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                        (dlBox ℓ d u) (p.1.succAbove j') Φ) x) ^ 2) := by
              ring
      rw [Finset.sum_congr rfl hper, ← Finset.mul_sum]

end Work.BoseFixB1S
