import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseFixB1S.pairSlotPeelB1
import Submission.Work.BoseFixB3.CS.Pieces.ppMass_le_q4mass_cnPlus_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.q4Mass_fibre_marginal`

The **fibre marginal identity** of the `4Q`-square of the pair `(i,j)`: integrating the pair
integrand `(q4B_p)²·w` over the two *inserted* coordinates `(y,z) ∈ Λ²` while the remaining
coordinates range over the box equals `ℓ⁶` times the box integral of the pair integrand of
the *given* configuration.

The mathematical content is one measure-theoretic bookkeeping: with `ins2 i j' y z r` the
configuration obtained from `r : X m` by inserting `y` in slot `i` and `z` in slot
`i.succAbove j'` (so that the two distinguished slots of `X (m+2)` are `i` and `j = i.succAbove j'`),

* `Fun.peelL` (junk-tolerant two-slot peel `abox_peel2_ins2`, applied to the box integral of the
  *inner* double integral) writes the left-hand side as the integral over
  `(Λ × Λ) × abox m ℓ` of an integrand which does not depend on the two inserted variables, so
  `integral_prod_mul` (also junk-tolerant) produces exactly the factor `vol (Λ × Λ) = ℓ⁶`;
* `hpeelR`, `hstepR2` peel the right-hand side and identify the two slots with the running
  variables; `integral_prod_symm` (Fubini, needing only the integrability of the joint
  integrand, transported from `IntegrableOn` over the box along the measure-preserving
  insertion `ins2_flat_mp`) turns it into an integral over `abox m ℓ` of the **slice**
  integrals, and `integral_prod` identifies each slice with the double cube integral.

The single genuine measure-theoretic input is the integrability of the box integrand
`x ↦ (q4B_p x)²·w(x_{p.1},x_{p.2})`, supplied in the application by the corpus lemma
`integrableOn_sq_mul_wLoc` (fed by the a.e.-bound of `ae_bounded_q4B_abox`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.CS.Pieces

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

/-- **The two-slot fibre marginal identity** (engine form).

For a kernel `w` on the two-particle cube and any pair observable `G` on the `(m+2)`-particle
box whose pair integrand `x ↦ G x · w (x i) (x (i.succAbove j'))` is integrable over the box,

`∫_x ∫_y ∫_z G (x with slots i,j replaced by y,z) · w y z  =  ℓ⁶ · ∫_x G x · w (x i) (x j)`. -/
theorem abox_fibre_marginal_engine {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (m + 2))
    (j' : Fin (m + 1)) (G : X (m + 2) → ℝ) (w : E3 → E3 → ℝ)
    (hIntOn : IntegrableOn (fun x : X (m + 2) => G x * w (x i) (x (i.succAbove j')))
      (Submission.BoseGases.abox (m + 2) ℓ) volume) :
    (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
        (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          G (Function.update (Function.update x i y) (i.succAbove j') z) * w y z))
      = ℓ ^ 6 * ∫ x in Submission.BoseGases.abox (m + 2) ℓ, G x * w (x i) (x (i.succAbove j')) := by
  -- ### Step 1: peel the box of the left-hand side (junk-tolerant)
  have hpeelL :
      (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
          (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
            G (Function.update (Function.update x i y) (i.succAbove j') z) * w y z))
        = ∫ q : (E3 × E3) × X m,
            (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
              G (Function.update (Function.update (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) i y)
                (i.succAbove j') z) * w y z)
          ∂(((volume.restrict (Submission.BoseGases.acube ℓ)).prod
              (volume.restrict (Submission.BoseGases.acube ℓ))).prod
            (volume.restrict (Submission.BoseGases.abox m ℓ))) :=
    Work.BoseFixB1S.abox_peel2_ins2 (m := m) hℓ i j'
      (fun x : X (m + 2) => ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
        G (Function.update (Function.update x i y) (i.succAbove j') z) * w y z)
  -- ### Step 2: re-inserting overwrites the two slots, so only the *rest* remains
  have hstep2 :
      (∫ q : (E3 × E3) × X m,
          (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
            G (Function.update (Function.update (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) i y)
              (i.succAbove j') z) * w y z)
        ∂(((volume.restrict (Submission.BoseGases.acube ℓ)).prod
            (volume.restrict (Submission.BoseGases.acube ℓ))).prod
          (volume.restrict (Submission.BoseGases.abox m ℓ))))
        = ∫ q : (E3 × E3) × X m,
            (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
              G (Submission.BoseGases.ins2 i j' y z q.2) * w y z)
          ∂(((volume.restrict (Submission.BoseGases.acube ℓ)).prod
              (volume.restrict (Submission.BoseGases.acube ℓ))).prod
            (volume.restrict (Submission.BoseGases.abox m ℓ))) := by
    apply integral_congr_ae
    filter_upwards with q
    apply integral_congr_ae
    filter_upwards with y
    apply integral_congr_ae
    filter_upwards with z
    rw [Submission.BoseGases.ins2_update_i, Submission.BoseGases.ins2_update_succ]
  -- ### Step 3: the two inserted slots contribute the volume `ℓ⁶` of `Λ × Λ`
  have hone : (∫ _p : E3 × E3, (1:ℝ)
      ∂((volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (volume.restrict (Submission.BoseGases.acube ℓ)))) = ℓ ^ 6 := by
    rw [MeasureTheory.integral_prod (f := fun _ : E3 × E3 => (1:ℝ)) (integrable_const (1:ℝ))]
    rw [Submission.BoseGases.integral_const_acube ℓ hℓ 1]
    rw [Submission.BoseGases.integral_const_acube ℓ hℓ (1 * ℓ ^ 3)]
    ring
  have hstep3 :
      (∫ q : (E3 × E3) × X m,
          (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
            G (Submission.BoseGases.ins2 i j' y z q.2) * w y z)
        ∂(((volume.restrict (Submission.BoseGases.acube ℓ)).prod
            (volume.restrict (Submission.BoseGases.acube ℓ))).prod
          (volume.restrict (Submission.BoseGases.abox m ℓ))))
        = ℓ ^ 6 * ∫ r : X m,
            (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
              G (Submission.BoseGases.ins2 i j' y z r) * w y z)
          ∂(volume.restrict (Submission.BoseGases.abox m ℓ)) := by
    have h1 : (fun q : (E3 × E3) × X m =>
          (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
            G (Submission.BoseGases.ins2 i j' y z q.2) * w y z))
        = fun q : (E3 × E3) × X m => (fun _ : E3 × E3 => (1:ℝ)) q.1 *
            (fun r : X m => (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
              G (Submission.BoseGases.ins2 i j' y z r) * w y z)) q.2 := by
      funext q; simp
    rw [h1, MeasureTheory.integral_prod_mul
      (μ := (volume.restrict (Submission.BoseGases.acube ℓ)).prod
        (volume.restrict (Submission.BoseGases.acube ℓ)))
      (ν := volume.restrict (Submission.BoseGases.abox m ℓ))
      (f := fun _ : E3 × E3 => (1:ℝ))
      (g := fun r : X m => (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
            G (Submission.BoseGases.ins2 i j' y z r) * w y z))]
    rw [hone]
  -- ### Step 4: the measure-preserving double insertion and the integrability transfer
  have hmp : MeasureTheory.MeasurePreserving
      (fun q : (E3 × E3) × X m => Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)
      (((volume.restrict (Submission.BoseGases.acube ℓ)).prod
          (volume.restrict (Submission.BoseGases.acube ℓ))).prod
        (volume.restrict (Submission.BoseGases.abox m ℓ)))
      (volume.restrict (Submission.BoseGases.abox (m + 2) ℓ)) :=
    Submission.BoseGases.ins2_flat_mp (p := m) hℓ i j'
  have hemb : MeasurableEmbedding
      (fun q : (E3 × E3) × X m => Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) := by
    have hfun : (fun q : (E3 × E3) × X m => Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)
        = (⇑(Submission.BoseGases.kcInsN (m + 1) i)) ∘
            (Prod.map id (⇑(Submission.BoseGases.kcInsN m j'))) ∘ ⇑(MeasurableEquiv.prodAssoc) := by
      funext q
      rcases q with ⟨⟨y, z⟩, r⟩
      rfl
    rw [hfun]
    exact ((MeasurableEquiv.measurableEmbedding (Submission.BoseGases.kcInsN (m + 1) i)).comp
      ((MeasurableEmbedding.prodMap MeasurableEmbedding.id
          (MeasurableEquiv.measurableEmbedding (Submission.BoseGases.kcInsN m j'))).comp
        (MeasurableEquiv.measurableEmbedding MeasurableEquiv.prodAssoc)))
  have hIntμ : Integrable
      (fun q : (E3 × E3) × X m => G (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) * w q.1.1 q.1.2)
      (((volume.restrict (Submission.BoseGases.acube ℓ)).prod
          (volume.restrict (Submission.BoseGases.acube ℓ))).prod
        (volume.restrict (Submission.BoseGases.abox m ℓ))) := by
    have hcomp := (hmp.integrable_comp_emb hemb
      (g := fun x : X (m + 2) => G x * w (x i) (x (i.succAbove j')))).mpr hIntOn
    refine hcomp.congr ?_
    filter_upwards with q
    simp only [Function.comp_apply]
    rw [Submission.BoseGases.ins2_apply_i, Submission.BoseGases.ins2_apply_succ]
  -- ### Step 5: peel the right-hand side and identify the inserted slots
  have hpeelR :
      (∫ x in Submission.BoseGases.abox (m + 2) ℓ, G x * w (x i) (x (i.succAbove j')))
        = ∫ q : (E3 × E3) × X m,
            G (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)
              * w ((Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) i)
                ((Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) (i.succAbove j'))
          ∂(((volume.restrict (Submission.BoseGases.acube ℓ)).prod
              (volume.restrict (Submission.BoseGases.acube ℓ))).prod
            (volume.restrict (Submission.BoseGases.abox m ℓ))) :=
    Work.BoseFixB1S.abox_peel2_ins2 (m := m) hℓ i j'
      (fun x : X (m + 2) => G x * w (x i) (x (i.succAbove j')))
  have hstepR2 :
      (∫ q : (E3 × E3) × X m,
            G (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)
              * w ((Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) i)
                ((Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) (i.succAbove j'))
          ∂(((volume.restrict (Submission.BoseGases.acube ℓ)).prod
              (volume.restrict (Submission.BoseGases.acube ℓ))).prod
            (volume.restrict (Submission.BoseGases.abox m ℓ))))
        = ∫ q : (E3 × E3) × X m,
            G (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) * w q.1.1 q.1.2
          ∂(((volume.restrict (Submission.BoseGases.acube ℓ)).prod
              (volume.restrict (Submission.BoseGases.acube ℓ))).prod
            (volume.restrict (Submission.BoseGases.abox m ℓ))) := by
    apply integral_congr_ae
    filter_upwards with q
    rw [Submission.BoseGases.ins2_apply_i, Submission.BoseGases.ins2_apply_succ]
  -- ### Step 6: Fubini over the rest, and the slice identification
  have hstepR3 :
      (∫ q : (E3 × E3) × X m,
            G (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) * w q.1.1 q.1.2
          ∂(((volume.restrict (Submission.BoseGases.acube ℓ)).prod
              (volume.restrict (Submission.BoseGases.acube ℓ))).prod
            (volume.restrict (Submission.BoseGases.abox m ℓ))))
        = ∫ r : X m,
            (∫ p : E3 × E3, G (Submission.BoseGases.ins2 i j' p.1 p.2 r) * w p.1 p.2
              ∂((volume.restrict (Submission.BoseGases.acube ℓ)).prod
                (volume.restrict (Submission.BoseGases.acube ℓ))))
          ∂(volume.restrict (Submission.BoseGases.abox m ℓ)) :=
    MeasureTheory.integral_prod_symm
      (f := fun q : (E3 × E3) × X m =>
        G (Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2) * w q.1.1 q.1.2) hIntμ
  have hstepR4 :
      (∫ r : X m,
            (∫ p : E3 × E3, G (Submission.BoseGases.ins2 i j' p.1 p.2 r) * w p.1 p.2
              ∂((volume.restrict (Submission.BoseGases.acube ℓ)).prod
                (volume.restrict (Submission.BoseGases.acube ℓ))))
          ∂(volume.restrict (Submission.BoseGases.abox m ℓ)))
        = ∫ r : X m,
            (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
              G (Submission.BoseGases.ins2 i j' y z r) * w y z)
          ∂(volume.restrict (Submission.BoseGases.abox m ℓ)) := by
    apply integral_congr_ae
    filter_upwards [hIntμ.prod_left_ae] with r hr
    exact MeasureTheory.integral_prod (μ := volume.restrict (Submission.BoseGases.acube ℓ))
      (ν := volume.restrict (Submission.BoseGases.acube ℓ))
      (f := fun p : E3 × E3 => G (Submission.BoseGases.ins2 i j' p.1 p.2 r) * w p.1 p.2) hr
  rw [hpeelL, hstep2, hstep3, hpeelR, hstepR2, hstepR3, hstepR4]

theorem q4Mass_fibre_marginal {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (R : ℝ) (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hav : 0 < BoseGases.a v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    ∫ x in Submission.BoseGases.abox n ℓ,
        (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j)
              (Function.update (Function.update x i y) j z)) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 y z)
      = ℓ ^ 6 * ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) x) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (x i) (x j) := by
  classical
  rcases n with _ | _ | m
  · exact Fin.elim0 i
  · exact absurd (Fin.ext (by omega)) hij
  · -- the two distinguished slots: `i` and `j = i.succAbove j'`
    obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
    rw [← hj']
    have hpne : i ≠ i.succAbove j' := (Fin.succAbove_ne i j').symm
    have hp : (i, i.succAbove j') ∈ Submission.BoseGases.pairSet (m + 2) := by
      rw [Submission.BoseGases.pairSet]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpne⟩
    obtain ⟨-, hqmeas, B, hB0, hqbnd⟩ :=
      ae_bounded_q4B_abox hv hvrad R hR hv_supp hav h hℓ hΦc hp
    have hv_int : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
    have hsuppv : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → v z = 0 := fun z hz =>
      Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz
    have hIntOn : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X (m + 2) =>
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ
              (i, i.succAbove j') x) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (x i) (x (i.succAbove j')))
        (Submission.BoseGases.abox (m + 2) ℓ) MeasureTheory.volume :=
      integrableOn_sq_mul_wLoc (n := m + 2) (p := (i, i.succAbove j'))
        hℓ hv_int hsuppv hRℓ hpne hqmeas hB0 hqbnd
    exact abox_fibre_marginal_engine hℓ i j'
      (fun x : Submission.BoseGases.X (m + 2) =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ
            (i, i.succAbove j') x) ^ 2)
      (fun y z => Submission.BoseGases.wLoc ℓ v 0 y z) hIntOn

end Work.BoseFixB3.CS.Pieces
