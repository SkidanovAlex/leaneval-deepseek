import Mathlib.MeasureTheory.Integral.Pi
import Submission.Work.ESYRound5.Energy.pairSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Peeling an interacting pair out of a product word

`Work.BoseKinLoc.Word.pair_peel` is the *unconditional* two-slot Fubini identity for a
product measure: for the two singled-out slots `a` and `a.succAbove b'` of
`Fin (k+2)`, an interaction kernel `g` coupling them, and a one-body factor `f` on
every slot,

    `∫ x, g (x a) (x (a.succAbove b')) * ∏ l, f (x l) ∂(Measure.pi (fun _ => μ))`
      `= (∫ z, f z ∂μ)^k * ∫ p, g p.1 p.2 * f p.1 * f p.2 ∂(μ.prod μ)`.

The remaining `k` slots contribute the `k`-th power of the one-body integral, exactly as
the pure product case `MeasureTheory.integral_fintype_prod_eq_pow`, while the two
singled-out slots are integrated with the product measure `μ.prod μ`.

The one interesting point is that **no measurability or integrability hypothesis on `f`
or `g` is needed**: the Bochner integral has the junk value `0` for non-a.e.-strongly-
measurable integrands, and every tool used below (`MeasurePreserving.integral_comp'` for
measurable equivalences, `MeasureTheory.integral_prod_mul`) is junk-compatible, so the
identity is unconditional.  (The companion `Work.ESYRound5.Energy.integral_pi_pair_mul`
proves the corresponding statement with a per-slot family of cuts and with an explicit
integrability hypothesis; here the point is precisely that no such hypothesis is needed.)

## The proof

The measure-preserving reindexing is the composition `Φ` of
* `e1`: split off the slot `a` — `MeasurableEquiv.piFinSuccAbove` at `a`, giving
  `(Fin (k+2) → α) ≃ᵐ α × (Fin (k+1) → α)`;
* `e2`: split off the slot `b'` of the remaining `k+1` slots, giving
  `(Fin (k+1) → α) ≃ᵐ α × (Fin k → α)`;
* the associativity identification `α × (α × (Fin k → α)) ≃ (α × α) × (Fin k → α)`.

The three measure-preservation statements are
`MeasureTheory.measurePreserving_piFinSuccAbove` (twice),
`MeasureTheory.MeasurePreserving.prod` and `MeasureTheory.Measure.prodAssoc_prod`.
Under `Φ` the integrand becomes `(g q.1.1 q.1.2 * f q.1.1 * f q.1.2) * ∏ i, f (q.2 i)`,
which is the product of a function of `q.1` and a function of `q.2`, so
`MeasureTheory.integral_prod_mul` factors the integral and
`MeasureTheory.integral_fintype_prod_eq_pow` evaluates the `k`-slot factor.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Word

theorem pair_peel {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]
    (k : ℕ) (a : Fin (k + 2)) (b' : Fin (k + 1)) (f : α → ℝ) (g : α → α → ℝ) :
    (∫ x : Fin (k + 2) → α, g (x a) (x (a.succAbove b')) * ∏ l, f (x l)
        ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 2) => μ)))
      = (∫ z : α, f z ∂μ) ^ k
          * (∫ p : α × α, g p.1 p.2 * f p.1 * f p.2 ∂(MeasureTheory.Measure.prod μ μ)) := by
  -- the two one-slot splittings and the associativity identification
  let e1 : (Fin (k + 2) → α) ≃ᵐ (α × (Fin (k + 1) → α)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) => α) a
  let e2 : (Fin (k + 1) → α) ≃ᵐ (α × (Fin k → α)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) b'
  let Φ : ((α × α) × (Fin k → α)) ≃ᵐ (Fin (k + 2) → α) :=
    MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) e2).symm.trans e1.symm)
  have h1 : MeasurePreserving (⇑e1) (Measure.pi (fun _ : Fin (k + 2) => μ))
      (μ.prod (Measure.pi (fun _ : Fin (k + 1) => μ))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (k + 2) => μ) a
  have h2 : MeasurePreserving (⇑e2) (Measure.pi (fun _ : Fin (k + 1) => μ))
      (μ.prod (Measure.pi (fun _ : Fin k => μ))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) b'
  have hpc : MeasurePreserving (⇑(MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) e2))
      (μ.prod (Measure.pi (fun _ : Fin (k + 1) => μ)))
      (μ.prod (μ.prod (Measure.pi (fun _ : Fin k => μ)))) := by
    have h := (MeasurePreserving.id μ).prod h2
    simpa [MeasurableEquiv.prodCongr] using h
  have hassoc : MeasurePreserving (⇑MeasurableEquiv.prodAssoc)
      ((μ.prod μ).prod (Measure.pi (fun _ : Fin k => μ)))
      (μ.prod (μ.prod (Measure.pi (fun _ : Fin k => μ)))) :=
    ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  have hΦfun : ⇑Φ = ⇑e1.symm ∘ ⇑((MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) e2).symm)
      ∘ ⇑MeasurableEquiv.prodAssoc := by
    funext q
    simp [Φ, MeasurableEquiv.trans_apply]
  have hΦ : MeasurePreserving (⇑Φ) ((μ.prod μ).prod (Measure.pi (fun _ : Fin k => μ)))
      (Measure.pi (fun _ : Fin (k + 2) => μ)) := by
    rw [hΦfun]
    exact (MeasurePreserving.symm e1 h1).comp
      ((MeasurePreserving.symm (MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) e2) hpc).comp
        hassoc)
  -- the integrand transported along `Φ` is a product of a function of `q.1` and one of `q.2`
  have hpt' : (fun x : (α × α) × (Fin k → α) => g (Φ x a) (Φ x (a.succAbove b')) * ∏ l, f (Φ x l))
      = (fun q : (α × α) × (Fin k → α) =>
          (g q.1.1 q.1.2 * f q.1.1 * f q.1.2) * ∏ i, f (q.2 i)) := by
    funext q
    obtain ⟨⟨y, z⟩, v⟩ := q
    have hkey : Φ ((y, z), v) = e1.symm (y, e2.symm (z, v)) := by
      simp [Φ, MeasurableEquiv.trans_apply, MeasurableEquiv.prodAssoc, MeasurableEquiv.prodCongr,
        MeasurableEquiv.refl]
    -- values of the transported configuration at the two singled-out slots
    have hya : (Φ ((y, z), v)) a = y := by
      rw [hkey]
      simp [e1, e2, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_apply_same]
    have hzb : (Φ ((y, z), v)) (a.succAbove b') = z := by
      rw [hkey]
      simp [e1, e2, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
    have hmid : (e2.symm (z, v)) b' = z := by
      simp [e2, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_apply_same]
    have hrow : ∀ j : Fin (k + 1), (Φ ((y, z), v)) (a.succAbove j) = (e2.symm (z, v)) j := by
      intro j
      rw [hkey]
      simp [e1, e2, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_apply_succAbove]
    have htail : ∀ i : Fin k, (e2.symm (z, v)) (b'.succAbove i) = v i := by
      intro i
      simp [e2, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_apply_succAbove]
    -- the full product of `f` factors through the `k+2`-slot, `k+1`-slot and `k`-slot splits
    have hprod : ∏ l, f ((Φ ((y, z), v)) l) = f y * (f z * ∏ i, f (v i)) := by
      rw [Fin.prod_univ_succAbove (fun l => f ((Φ ((y, z), v)) l)) a, hya]
      simp only [hrow]
      rw [Fin.prod_univ_succAbove (fun j => f ((e2.symm (z, v)) j)) b', hmid]
      simp only [htail]
    show g (Φ ((y, z), v) a) (Φ ((y, z), v) (a.succAbove b')) * ∏ l, f (Φ ((y, z), v) l) = _
    rw [hya, hzb, hprod]
    ring
  rw [← MeasurePreserving.integral_comp' hΦ
    (fun x : Fin (k + 2) → α => g (x a) (x (a.succAbove b')) * ∏ l, f (x l))]
  rw [hpt']
  -- factor over the product `(α × α) × (Fin k → α)` and evaluate the `k`-slot integral
  refine (MeasureTheory.integral_prod_mul (μ := μ.prod μ)
      (ν := Measure.pi (fun _ : Fin k => μ))
      (f := fun p : α × α => g p.1 p.2 * f p.1 * f p.2)
      (g := fun v : Fin k → α => ∏ i, f (v i))).trans ?_
  simp only [MeasureTheory.integral_fintype_prod_eq_pow, Fintype.card_fin]
  ring

end Work.BoseKinLoc.Word
