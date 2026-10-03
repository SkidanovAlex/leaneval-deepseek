import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.Gates
import Submission.Work.Pert.coordP_level_eq

/-!
# PERT · `Work.Pert.RBlock7.retPPhi`: the paper's `R̃_f` has `φ_f ∘ R̃_f = φ_f` **by construction**

Shishikura's lifted return map is `R̃_f = Φ_{-,f} ∘ T_f ∘ Φ_{-,f}⁻¹`, and the identity
`φ_f ∘ R̃_f = φ_f` (his (4.3.4), and the hypothesis that drives the orbit relation (4.2.3)) is then
the triviality `τ_f ∘ T_f = τ_f`.  In the maximal-domain language of `Work.Pert.MaxDom` the same map
is the **level-preserving** one

  `Work.Pert.retP f Df τ Φ Q α w = n_w + Φ (Tt α (Φ⁻¹ (w - n_w)))`,
  `n_w = mIdxP f Df τ Φ Q w`,

and the identity becomes: *the level-`n_w` seed of `R̃ w` is `τ (Tt α ς_w) = τ ς_w`, which is the
level-`n_w` seed of `w`* — so the two `coordP` values agree by the level-independence
`Work.Pert.coordP_level_eq`.

The level structure has to be taken on the **waist** `Qm Ξ α ∩ Qp Ξ α`: only there does
`Tt α ς_w ∈ Qm Ξ α` hold (`Work.Pert.Tt_mem_Qm_iff`, i.e. `ς_w ∈ Qp Ξ α`), which is what makes
`Φ (Tt α ς_w)` a genuine value of the gate coordinate; while the *value* `coordP` is read in the
full gate `Qm Ξ α` (the maximal domain of `φ_f`).
-/

namespace Work.Pert.RBlock7

open _root_.MandelDim Complex Set

noncomputable section

/-- **The paper's return map preserves `φ_f`.**  Let `Φ` be a gate coordinate for `F = liftF u σ α`
on `Qm Ξ α`, `Wa = Qm Ξ α ∩ Qp Ξ α` the waist, and suppose `w` is a legal `Wa`-level point whose
gate point satisfies the one structural fact `τ (Tt α ·) = τ ·` (in the applications this is
`Work.Pert.tauC_add_period`).  Then the level-preserving return map `retP f Df τ Φ Wa α` fixes the
value of `φ_f = coordP f Df τ Φ (Qm Ξ α)`. -/
theorem retP_phi_eq {f F τ Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {Df : Set ℂ} {w : ℂ}
    (hinj : Set.InjOn Φ (Work.Pert.Qm Ξ α))
    (hab : ∀ z ∈ Work.Pert.Qm Ξ α, F z ∈ Work.Pert.Qm Ξ α → Φ (F z) = Φ z + 1)
    (hτF : ∀ z ∈ Work.Pert.Qm Ξ α, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Work.Pert.Qm Ξ α, ∀ z' ∈ Work.Pert.Qm Ξ α, ∀ k : ℕ,
      Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Work.Pert.Qm Ξ α) ∧ F^[k] z = z')
    (hτT : ∀ x : ℂ, τ (Work.Pert.Tt α x) = τ x)
    (hgoodWa : Work.Pert.GoodP f Df τ Φ
      (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w) :
    Work.Pert.coordP f Df τ Φ (Work.Pert.Qm Ξ α)
        (Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) α w)
      = Work.Pert.coordP f Df τ Φ (Work.Pert.Qm Ξ α) w := by
  classical
  -- the gate point `ς` of `w` at its minimal waist level `n`
  obtain ⟨himg, hwalk⟩ := Work.Pert.mIdxP_spec hgoodWa
  obtain ⟨ς, hςWa, hςΦ⟩ := himg
  have hςQm : ς ∈ Work.Pert.Qm Ξ α := hςWa.1
  have hςQp : ς ∈ Work.Pert.Qp Ξ α := hςWa.2
  have hinjWa : Set.InjOn Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) := hinj.mono inter_subset_left
  -- `τ` of the deck translate of `ς` is `τ ς`
  have hτTς : τ (Work.Pert.Tt α ς) = τ ς := hτT ς
  -- the deck translate of `ς` is a gate point (`Tt_mem_Qm_iff`, from `ς ∈ Qp Ξ α`)
  have hTtςQm : Work.Pert.Tt α ς ∈ Work.Pert.Qm Ξ α :=
    Work.Pert.Tt_mem_Qm_iff.mpr hςQp
  -- the seeds at level `n` of `w` (waist) and of `Tt α ς` (gate) are the same number `τ ς`
  have hseedWa : Work.Pert.seedP τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)
      (w - (Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w : ℂ)) = τ ς :=
    Work.Pert.seedP_eq_of_mem' hinjWa ⟨ς, hςWa, hςΦ⟩ hςWa hςΦ
  have hval : Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) α w
      - (Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w : ℂ)
      = Φ (Work.Pert.Tt α ς) := by
    simp only [Work.Pert.retP]
    rw [Work.Pert.invOn_eq hinjWa ⟨ς, hςWa, hςΦ⟩ hςWa hςΦ]
    ring
  have hseedQm : Work.Pert.seedP τ Φ (Work.Pert.Qm Ξ α)
      (Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) α w
        - (Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w : ℂ))
      = τ (Work.Pert.Tt α ς) := by
    rw [hval]
    exact Work.Pert.seedP_eq_of_mem' hinj ⟨Work.Pert.Tt α ς, hTtςQm, rfl⟩ hTtςQm rfl
  -- the gate seed of `w` at level `n` is the same number
  have hseedQmw : Work.Pert.seedP τ Φ (Work.Pert.Qm Ξ α)
      (w - (Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w : ℂ)) = τ ς :=
    Work.Pert.seedP_eq_of_mem' hinj ⟨ς, hςQm, hςΦ⟩ hςQm hςΦ
  -- `R w` is a legal gate level-`n` point of `w`
  have hgoodRm : Work.Pert.GoodP f Df τ Φ (Work.Pert.Qm Ξ α)
      (Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) α w) := by
    refine ⟨Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w, ?_, ?_⟩
    · exact ⟨Work.Pert.Tt α ς, hTtςQm, hval.symm⟩
    · intro j hj
      rw [hseedQm, hτTς]
      have h := hwalk j hj
      rwa [hseedWa] at h
  -- the walk seeds
  have hτςDf : ∀ j : ℕ, j < Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w →
      f^[j] (τ ς) ∈ Df := by
    intro j hj
    have h := hwalk j hj
    rwa [hseedWa] at h
  have hτTtDf : ∀ j : ℕ, j < Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w →
      f^[j] (τ (Work.Pert.Tt α ς)) ∈ Df := by
    intro j hj
    rw [hτTς]
    exact hτςDf j hj
  -- both coordinates are computed at the legal level `n`
  have hlevel_w : Work.Pert.coordP f Df τ Φ (Work.Pert.Qm Ξ α) w = f^[
      Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w] (τ ς) :=
    Work.Pert.coordP_level_eq (f := f) (Df := Df) (F := F) (τ := τ) (Φ := Φ)
      (Q := Work.Pert.Qm Ξ α) hinj hab hτF hOrb
      ⟨_, ⟨ς, hςQm, hςΦ⟩, fun j hj => by rw [hseedQmw]; exact hτςDf j hj⟩
      hςQm hςΦ hτςDf
  have hlevel_R : Work.Pert.coordP f Df τ Φ (Work.Pert.Qm Ξ α)
      (Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) α w)
      = f^[Work.Pert.mIdxP f Df τ Φ (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) w]
          (τ (Work.Pert.Tt α ς)) :=
    Work.Pert.coordP_level_eq (f := f) (Df := Df) (F := F) (τ := τ) (Φ := Φ)
      (Q := Work.Pert.Qm Ξ α) hinj hab hτF hOrb hgoodRm hTtςQm hval.symm hτTtDf
  rw [hlevel_R, hlevel_w, hτTς]

end

end Work.Pert.RBlock7
