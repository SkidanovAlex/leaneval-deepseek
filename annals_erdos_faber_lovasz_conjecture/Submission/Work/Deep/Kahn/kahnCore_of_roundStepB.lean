/-
# Kahn's Theorem from the colour-degree one-round nibble step

`kahnCore_of_roundStepB : RoundStepStatement → KahnCoreStatement`, i.e. the *iteration* of
the one-round step of the colour-degree nibble
(`Submission/Work/Deep/Kahn/NibbleRoundDefs.lean`) proving Kahn's list-edge-colouring theorem
for linear hypergraphs whose edges have size at least two.

The one-round step consumes a state `(𝓗, L, Λ, D)` — linear, rank `≤ C`, lists of common size
`Λ`, colour degrees at most `D`, ratio `ρ = Λ/D ≥ 1 + ε` — and produces a partial colouring
plus residual lists with `|L' e| ≥ newLambda Λ C D K - η Λ` and colour degrees
`≤ newDeg Λ C D K + η D`.  The arithmetic core (`retention_gain`, `retention_recurrence`)
shows that `ρ` grows by a factor `1 + γ` (`γ = ε/(4K)`) per round while `D` drops by
`(1/K)(1 + (C-1)/ρ)`.  Because the `D`-drop is not uniform in the round, the iteration tracks
the potential `Ψ = log Λ - b(D/Λ)` with `b = 32 C/ε + 1`: the `1/ρ`-losses of `D` telescope
against the geometric growth of `ρ`, so `Ψ` drops by at most `8 η` per round.  Hence `D` drops
by at most the *constant* factor `exp (-(34 C/ε + 4))` over all `T` rounds.

After `T` rounds the ratio is at least `8 C`; the residual lists are then long compared with the
colour degrees and `finishing_step` (Reed's list-colouring constants) colours the remainder.
`RoundCore.exists_coloring_of_partial` glues the per-round partial colourings.
-/
import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.NibbleRoundDefs
import Submission.Work.Deep.Kahn.Defs
import Submission.Work.Deep.Kahn.finishing_step
import Submission.Work.Deep.Kahn.kahnCore_of_round
import Submission.Work.Deep.Kahn.listColorable_of_card_gt_sum_degree
import Submission.Work.Deep.Kahn.IterDefs
import Submission.Work.Deep.Kahn.GrowthBound
import Submission.Work.Deep.Kahn.retention_gain
import Submission.Work.Deep.Kahn.retention_recurrence
import Submission.Work.Deep.Kahn.mkIt_cond
import Submission.Work.Deep.Kahn.pot_step

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

/-! ## 1.  The one-round statement, written as a standalone `Prop` -/

/-- The conclusion of one round of the nibble, as a `Prop`. -/
abbrev RoundOutcome {n c : ℕ} (C : ℕ) (ε η : ℝ)
    (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (L : 𝓗 → Finset (Fin c))
    (D Λ K : ℕ) : Prop :=
  ∃ (𝓗₀ : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (hsub : 𝓗₀ ⊆ 𝓗)
    (φ : 𝓗₀.Coloring (Fin c))
    (L' : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type) → Finset (Fin c)),
    (∀ e : 𝓗₀, φ.labels e ∈ L ⟨(e : Set (Fin n)), hsub e.2⟩) ∧
    (∀ e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type),
        L' e ⊆ L ⟨(e : Set (Fin n)), e.2.1⟩) ∧
    (∀ e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type),
        newLambda Λ C D K - η * (Λ : ℝ) ≤ ((L' e).card : ℝ)) ∧
    (∀ e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type), ∀ f : 𝓗₀,
        (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty → φ.labels f ∉ L' e)) ∧
    (∀ x : Fin n, ∀ γ : Fin c,
        ((Nat.card {e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type) //
            x ∈ (e : Set (Fin n)) ∧ γ ∈ L' e} : ℕ) : ℝ) ≤ newDeg Λ C D K + η * (D : ℝ))

/-- The one-round statement with its threshold `Dmin` fixed. -/
abbrev RoundProp (C : ℕ) (ε η : ℝ) (Dmin : ℝ) : Prop :=
  ∀ (n c : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (L : 𝓗 → Finset (Fin c)) (D Λ K : ℕ),
    1 ≤ D → 1 ≤ Λ → 2 ≤ K → η * (K : ℝ) ≤ 1 →
    (16 : ℝ) * (C : ℝ) ≤ (1 + ε) * (K : ℝ) →
    𝓗.IsLinear →
    (∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ C) →
    (∀ e : 𝓗, (L e).card = Λ) →
    (∀ x : Fin n, ∀ γ : Fin c,
      Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} ≤ D) →
    (1 + ε) * (D : ℝ) ≤ (Λ : ℝ) → (Λ : ℝ) ≤ 10 * (C : ℝ) * (D : ℝ) →
    Dmin ≤ (D : ℝ) →
    Real.log (D : ℝ) ≤ (K : ℝ) → (K : ℝ) ≤ (Real.log (D : ℝ)) ^ 2 →
    ((C : ℝ) + (K : ℝ) + η⁻¹) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) →
    RoundOutcome C ε η 𝓗 L D Λ K

/-- `RoundStepStatement` gives, for every `C`, `ε`, `η`, a threshold `Dmin` carrying
`RoundProp`. -/
lemma roundProp_of (h : RoundStepStatement) (C : ℕ) (hC : 2 ≤ C) (ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) : ∃ Dmin : ℝ, 0 < Dmin ∧ RoundProp C ε η Dmin := by
  obtain ⟨Dm, hDm0, -, hDm⟩ := h C hC ε η hε hη
  refine ⟨Dm, hDm0, ?_⟩
  intro n c 𝓗 L D Λ K h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  exact hDm n c 𝓗 L D Λ K h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15

/-! ## 2.  The invariant of the iteration -/

/-- The state invariant of the iteration: a partial colouring `f` of `𝓗`, residual lists `L'`
of common size `Λ` on the uncoloured edges, colour degrees at most `D`, plus the numerical
invariants: growth of the ratio, the potential `log Λ - b (D/Λ)`, `D ≤ D₀`, and `i ≤ T`. -/
structure Inv (it : It) {n c : ℕ} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (L : 𝓗 → Finset (Fin c)) (i : ℕ) (f : Set (Fin n) → Option (Fin c))
    (L' : Set (Fin n) → Finset (Fin c)) (Λ D : ℕ) : Prop where
  hout : ∀ e, e ∉ 𝓗 → f e = none
  hsub : ∀ (e : Set (Fin n)) (he : e ∈ 𝓗), L' e ⊆ L ⟨e, he⟩
  hmem : ∀ (e : Set (Fin n)) (he : e ∈ 𝓗) (γ : Fin c), f e = some γ → γ ∈ L ⟨e, he⟩
  hproper : ∀ (e₁ e₂ : Set (Fin n)) (γ₁ γ₂ : Fin c), f e₁ = some γ₁ → f e₂ = some γ₂ →
    e₁ ≠ e₂ → (e₁ ∩ e₂ : Set (Fin n)).Nonempty → γ₁ ≠ γ₂
  hexcl : ∀ (e : Set (Fin n)) (he : e ∈ 𝓗), f e = none → ∀ γ : Fin c,
    (∃ v ∈ e, ∃ e' ∈ 𝓗, f e' = some γ ∧ v ∈ e') → γ ∉ L' e
  hcard : ∀ (e : Set (Fin n)) (he : e ∈ 𝓗), f e = none → (L' e).card = Λ
  hdeg : ∀ (x : Fin n) (γ : Fin c),
    ((Nat.card {e : (RoundCore.uncoloured 𝓗 f : Set (Set (Fin n))) //
        x ∈ (e : Set (Fin n)) ∧ γ ∈ L' (e : Set (Fin n))} : ℕ) : ℝ) ≤ (D : ℝ)
  hD1 : 1 ≤ D
  hiT : i ≤ it.T
  hpot : Real.log (Λ : ℝ) - it.b * ((D : ℝ) / (Λ : ℝ)) ≥
    Real.log (it.Λ0 : ℝ) - it.b * ((it.Di0 : ℝ) / (it.Λ0 : ℝ)) - 8 * it.η * (i : ℝ)
  hρ10 : (Λ : ℝ) / (D : ℝ) ≤ 10 * (it.C : ℝ)
  hρmin : min (8 * (it.C : ℝ)) (it.ρ0 * (1 + it.γ₁) ^ i) ≤ (Λ : ℝ) / (D : ℝ)
  hDle : (D : ℝ) ≤ (it.Di0 : ℝ)

namespace Inv

/-- The ratio is at least `1 + ε` at every time. -/
lemma ratio_ge (it : It) {Dm : ℝ} (hcond : it.Cond Dm) {n c : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} {L : 𝓗 → Finset (Fin c)}
    {i : ℕ} {f : Set (Fin n) → Option (Fin c)} {L' : Set (Fin n) → Finset (Fin c)}
    {Λ D : ℕ} (hinv : Inv it 𝓗 L i f L' Λ D) :
    (1 + it.ε) * (D : ℝ) ≤ (Λ : ℝ) := by
  obtain ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb, hT8, hεDi0, hΛ10,
    hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩ := hcond
  have hDi0pos : (0 : ℝ) < (it.Di0 : ℝ) := by
    have h : (1 : ℝ) ≤ (it.Di0 : ℝ) := by exact_mod_cast hDi0
    linarith
  have hΛ0pos : (0 : ℝ) < (it.Λ0 : ℝ) := by
    have h : (1 : ℝ) ≤ (it.Λ0 : ℝ) := by exact_mod_cast hΛ0
    linarith
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have h : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hinv.hD1
    linarith
  have hρ0 : (1 + it.ε) ≤ it.ρ0 := by
    rw [It.ρ0_eq, le_div_iff₀ hDi0pos]
    exact hεDi0
  have hρ0pos : (0 : ℝ) < it.ρ0 := by
    rw [It.ρ0_eq]; exact div_pos hΛ0pos hDi0pos
  have hpow : (1 : ℝ) ≤ (1 + it.γ₁) ^ i :=
    one_le_pow₀ (by rw [It.γ₁_eq]; linarith)
  have hC2 : (2 : ℝ) ≤ (it.C : ℝ) := by exact_mod_cast hC
  have hmin : (1 + it.ε) ≤ min (8 * (it.C : ℝ)) (it.ρ0 * (1 + it.γ₁) ^ i) := by
    apply le_min
    · linarith
    · calc (1 + it.ε) = (1 + it.ε) * 1 := by ring
        _ ≤ it.ρ0 * (1 + it.γ₁) ^ i :=
            mul_le_mul hρ0 hpow (by norm_num) (le_of_lt hρ0pos)
  have hρ : (1 + it.ε) ≤ (Λ : ℝ) / (D : ℝ) := le_trans hmin hinv.hρmin
  calc (1 + it.ε) * (D : ℝ) ≤ ((Λ : ℝ) / (D : ℝ)) * (D : ℝ) :=
        mul_le_mul_of_nonneg_right hρ (le_of_lt hDpos)
    _ = (Λ : ℝ) := by field_simp

/-- `D` is at least `Dlow`, the uniform lower bound of the iteration. -/
lemma Dlow_le (it : It) {Dm : ℝ} (hcond : it.Cond Dm) {n c : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} {L : 𝓗 → Finset (Fin c)}
    {i : ℕ} {f : Set (Fin n) → Option (Fin c)} {L' : Set (Fin n) → Finset (Fin c)}
    {Λ D : ℕ} (hinv : Inv it 𝓗 L i f L' Λ D) : it.Dlow ≤ (D : ℝ) := by
  obtain ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb, hT8, hεDi0, hΛ10,
    hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩ := hcond
  have hcon : it.Cond Dm := ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb,
    hT8, hεDi0, hΛ10, hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩
  have hDi0pos : (0 : ℝ) < (it.Di0 : ℝ) := by
    have h : (1 : ℝ) ≤ (it.Di0 : ℝ) := by exact_mod_cast hDi0
    linarith
  have hΛ0pos : (0 : ℝ) < (it.Λ0 : ℝ) := by
    have h : (1 : ℝ) ≤ (it.Λ0 : ℝ) := by exact_mod_cast hΛ0
    linarith
  have hD1' : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hinv.hD1
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := by
    have h := hinv.ratio_ge it hcon
    nlinarith [hε0, hD1']
  have hb0 : (0 : ℝ) ≤ it.b := by
    have h1 : (0 : ℝ) ≤ 32 * (it.C : ℝ) / it.ε := by positivity
    linarith
  have hDΛ : (0 : ℝ) ≤ (D : ℝ) / (Λ : ℝ) := by
    apply div_nonneg <;> positivity
  have hDi0le : (it.Di0 : ℝ) ≤ (it.Λ0 : ℝ) := by
    have hDi0nn : (0 : ℝ) ≤ (it.Di0 : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have h1 : (it.Di0 : ℝ) ≤ (1 + it.ε) * (it.Di0 : ℝ) := by nlinarith [hε0, hDi0nn]
    linarith
  have hbDi : it.b * ((it.Di0 : ℝ) / (it.Λ0 : ℝ)) ≤ it.b := by
    have h1 : ((it.Di0 : ℝ) / (it.Λ0 : ℝ)) ≤ 1 := by
      rw [div_le_one hΛ0pos]; exact hDi0le
    calc it.b * ((it.Di0 : ℝ) / (it.Λ0 : ℝ)) ≤ it.b * 1 := mul_le_mul_of_nonneg_left h1 hb0
      _ = it.b := by ring
  have hηi : 8 * it.η * (i : ℝ) ≤ 8 * it.η * (it.T : ℝ) := by
    have h2 : (i : ℝ) ≤ (it.T : ℝ) := by exact_mod_cast hinv.hiT
    nlinarith [hη0]
  have hlog : Real.log (it.Λ0 : ℝ) - (it.b + 8 * it.η * (it.T : ℝ)) ≤ Real.log (Λ : ℝ) := by
    have h1 := hinv.hpot
    linarith [mul_nonneg hb0 hDΛ]
  have hexpΛ : Real.exp (Real.log (it.Λ0 : ℝ) - (it.b + 8 * it.η * (it.T : ℝ)))
      = (it.Λ0 : ℝ) * Real.exp (-(it.b + 8 * it.η * (it.T : ℝ))) := by
    rw [Real.exp_sub, Real.exp_log hΛ0pos, div_eq_mul_inv, Real.exp_neg]
  have hA : (it.Di0 : ℝ) * Real.exp (-(it.b + 8 * it.η * (it.T : ℝ))) ≤ (Λ : ℝ) := by
    have h1 : Real.exp (Real.log (it.Λ0 : ℝ) - (it.b + 8 * it.η * (it.T : ℝ))) ≤ (Λ : ℝ) := by
      have h2 := Real.exp_le_exp.mpr hlog
      rwa [Real.exp_log hΛpos] at h2
    refine le_trans ?_ h1
    rw [hexpΛ]
    exact mul_le_mul_of_nonneg_right hDi0le (by positivity)
  have hB : (Λ : ℝ) / (10 * (it.C : ℝ)) ≤ (D : ℝ) := by
    have h := hinv.hρ10
    have hDpos : (0 : ℝ) < (D : ℝ) := by linarith
    rw [div_le_iff₀ hDpos] at h
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 10 * (it.C : ℝ))]
    linarith
  have hE : Real.exp (-(34 * (it.C : ℝ) / it.ε + 4))
      ≤ 2 * Real.exp (-(it.b + 8 * it.η * (it.T : ℝ))) := by
    have h1 : -(34 * (it.C : ℝ) / it.ε + 4) ≤ -(it.b + 8 * it.η * (it.T : ℝ)) := by
      linarith [hηTb]
    have h2 : Real.exp (-(it.b + 8 * it.η * (it.T : ℝ)))
        ≤ 2 * Real.exp (-(it.b + 8 * it.η * (it.T : ℝ))) := by
      nlinarith [Real.exp_pos (-(it.b + 8 * it.η * (it.T : ℝ)))]
    exact le_trans (Real.exp_le_exp.mpr h1) h2
  have hCPos : (0 : ℝ) < (it.C : ℝ) := by exact_mod_cast (by omega : 0 < it.C)
  have hDlow_le : it.Dlow
      ≤ (it.Di0 : ℝ) * Real.exp (-(it.b + 8 * it.η * (it.T : ℝ))) / (10 * (it.C : ℝ)) := by
    rw [It.Dlow_eq]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 20 * (it.C:ℝ)), div_mul_eq_mul_div,
      le_div_iff₀ (by positivity : (0:ℝ) < 10 * (it.C:ℝ))]
    calc (it.Di0 : ℝ) * Real.exp (-(34 * (it.C : ℝ) / it.ε + 4)) * (10 * (it.C : ℝ))
        ≤ (it.Di0 : ℝ) * (2 * Real.exp (-(it.b + 8 * it.η * (it.T : ℝ)))) * (10 * (it.C : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hE (by positivity)
      _ = (it.Di0 : ℝ) * Real.exp (-(it.b + 8 * it.η * (it.T : ℝ))) * (20 * (it.C : ℝ)) := by ring
  calc it.Dlow ≤ (it.Di0 : ℝ) * Real.exp (-(it.b + 8 * it.η * (it.T : ℝ))) / (10 * (it.C : ℝ)) :=
        hDlow_le
    _ ≤ (Λ : ℝ) / (10 * (it.C : ℝ)) := div_le_div_of_nonneg_right hA (by positivity)
    _ ≤ (D : ℝ) := hB

/-- `η * D ≥ 1`. -/
lemma etaD_ge_one (it : It) {Dm : ℝ} (hcond : it.Cond Dm) {n c : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} {L : 𝓗 → Finset (Fin c)}
    {i : ℕ} {f : Set (Fin n) → Option (Fin c)} {L' : Set (Fin n) → Finset (Fin c)}
    {Λ D : ℕ} (hinv : Inv it 𝓗 L i f L' Λ D) : 1 ≤ it.η * (D : ℝ) := by
  obtain ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb, hT8, hεDi0, hΛ10,
    hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩ := hcond
  have hcon : it.Cond Dm := ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb,
    hT8, hεDi0, hΛ10, hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩
  have h1 : it.η⁻¹ ≤ (D : ℝ) := le_trans hηinv (hinv.Dlow_le it hcon)
  have h2 : it.η * it.η⁻¹ = 1 := by field_simp
  calc (1 : ℝ) = it.η * it.η⁻¹ := h2.symm
    _ ≤ it.η * (D : ℝ) := mul_le_mul_of_nonneg_left h1 (le_of_lt hη0)

/-- `16 * K ≤ D`. -/
lemma K_le_D (it : It) {Dm : ℝ} (hcond : it.Cond Dm) {n c : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} {L : 𝓗 → Finset (Fin c)}
    {i : ℕ} {f : Set (Fin n) → Option (Fin c)} {L' : Set (Fin n) → Finset (Fin c)}
    {Λ D : ℕ} (hinv : Inv it 𝓗 L i f L' Λ D) : 16 * (it.K : ℝ) ≤ (D : ℝ) := by
  obtain ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb, hT8, hεDi0, hΛ10,
    hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩ := hcond
  have hcon : it.Cond Dm := ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb,
    hT8, hεDi0, hΛ10, hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩
  exact le_trans h16K (hinv.Dlow_le it hcon)

/-- `1 ≤ D`. -/
lemma D_ge_one (it : It) {Dm : ℝ} (hcond : it.Cond Dm) {n c : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} {L : 𝓗 → Finset (Fin c)}
    {i : ℕ} {f : Set (Fin n) → Option (Fin c)} {L' : Set (Fin n) → Finset (Fin c)}
    {Λ D : ℕ} (hinv : Inv it 𝓗 L i f L' Λ D) : 1 ≤ D := hinv.hD1

/-- `log D ≤ K`. -/
lemma logD_le (it : It) {Dm : ℝ} (hcond : it.Cond Dm) {n c : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} {L : 𝓗 → Finset (Fin c)}
    {i : ℕ} {f : Set (Fin n) → Option (Fin c)} {L' : Set (Fin n) → Finset (Fin c)}
    {Λ D : ℕ} (hinv : Inv it 𝓗 L i f L' Λ D) : Real.log (D : ℝ) ≤ (it.K : ℝ) := by
  obtain ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb, hT8, hεDi0, hΛ10,
    hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩ := hcond
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have h : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hinv.hD1
    linarith
  exact le_trans (Real.log_le_log hDpos hinv.hDle) hlogDi0

/-- `K ≤ (log D)^2`. -/
lemma K_le_log_sq (it : It) {Dm : ℝ} (hcond : it.Cond Dm) {n c : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} {L : 𝓗 → Finset (Fin c)}
    {i : ℕ} {f : Set (Fin n) → Option (Fin c)} {L' : Set (Fin n) → Finset (Fin c)}
    {Λ D : ℕ} (hinv : Inv it 𝓗 L i f L' Λ D) :
    (it.K : ℝ) ≤ (Real.log (D : ℝ)) ^ 2 := by
  obtain ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb, hT8, hεDi0, hΛ10,
    hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩ := hcond
  have hcon : it.Cond Dm := ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb,
    hT8, hεDi0, hΛ10, hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩
  have hDle := hinv.Dlow_le it hcon
  have h16 : (16 : ℝ) * (it.K : ℝ) ≤ (D : ℝ) := hinv.K_le_D it hcon
  have hK1 : (1 : ℝ) ≤ (it.K : ℝ) := by
    have h : (2 : ℝ) ≤ (it.K : ℝ) := by exact_mod_cast hK
    linarith
  have hDpos : (0 : ℝ) < (D : ℝ) := by linarith
  have hlog : 2 * Real.sqrt (it.K : ℝ) ≤ Real.log (D : ℝ) := by
    have h1 : Real.exp (2 * Real.sqrt (it.K : ℝ)) ≤ (D : ℝ) := le_trans hexp hDle
    have h2 := Real.log_le_log (Real.exp_pos (2 * Real.sqrt (it.K : ℝ))) h1
    rwa [Real.log_exp] at h2
  have hK0 : (0 : ℝ) ≤ (it.K : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have h4 : 4 * (it.K : ℝ) ≤ (Real.log (D : ℝ)) ^ 2 := by
    have hsqrtK : (0 : ℝ) ≤ 2 * Real.sqrt (it.K : ℝ) := by
      have := Real.sqrt_nonneg (it.K : ℝ)
      linarith
    have h2 : (2 * Real.sqrt (it.K : ℝ)) ^ 2 ≤ (Real.log (D : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hsqrtK hlog 2
    rw [mul_pow, Real.sq_sqrt hK0] at h2
    norm_num at h2
    exact h2
  linarith

end Inv
/-- `(x^9)^(1/9) = x` for `x ≥ 0`. -/
lemma rpow_nine_inv (x : ℝ) (hx : 0 ≤ x) : (x ^ (9 : ℕ)) ^ ((1 : ℝ) / 9) = x := by
  rw [show (1 : ℝ) / 9 = ((9 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast hx (by norm_num)

/-! ## 3.  Initialisation and finishing -/

/-- **Initialisation.**  Given a list assignment whose lists are at least as long as `Λ₀` and
whose colour degrees are at most `D₀`, the truncated lists of common size `Λ₀` give a state of
the iteration at time `0`. -/
lemma init (it : It) {Dm : ℝ} (hcond : it.Cond Dm) {n c : ℕ}
    (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (L : 𝓗 → Finset (Fin c))
    (hL : ∀ e : 𝓗, (it.Λ0 : ℝ) ≤ ((L e).card : ℝ))
    (hdeg0 : ∀ x : Fin n, ∀ γ : Fin c,
      ((Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} : ℕ) : ℝ) ≤ (it.Di0 : ℝ)) :
    ∃ (f : Set (Fin n) → Option (Fin c)) (L' : Set (Fin n) → Finset (Fin c)) (Λ D : ℕ),
      Inv it 𝓗 L 0 f L' Λ D := by
  obtain ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb, hT8, hεDi0, hΛ10,
    hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩ := hcond
  classical
  have hex : ∀ (e : Set (Fin n)) (he : e ∈ 𝓗),
      ∃ t : Finset (Fin c), t ⊆ L ⟨e, he⟩ ∧ t.card = it.Λ0 := by
    intro e he
    exact Finset.exists_subset_card_eq (by exact_mod_cast hL ⟨e, he⟩)
  let L' : Set (Fin n) → Finset (Fin c) :=
    fun e => if h : e ∈ 𝓗 then Classical.choose (hex e h) else ∅
  have hL'sub : ∀ (e : Set (Fin n)) (he : e ∈ 𝓗), L' e ⊆ L ⟨e, he⟩ := by
    intro e he
    have h : L' e = Classical.choose (hex e he) := by simp only [L', dif_pos he]
    rw [h]; exact (Classical.choose_spec (hex e he)).1
  have hL'card : ∀ (e : Set (Fin n)) (he : e ∈ 𝓗), (L' e).card = it.Λ0 := by
    intro e he
    have h : L' e = Classical.choose (hex e he) := by simp only [L', dif_pos he]
    rw [h]; exact (Classical.choose_spec (hex e he)).2
  refine ⟨fun _ => (none : Option (Fin c)), L', it.Λ0, it.Di0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro e _
    rfl
  · exact hL'sub
  · intro e he γ hf
    exact absurd hf (by simp)
  · intro e₁ e₂ γ₁ γ₂ h₁ _ _ _
    exact absurd h₁ (by simp)
  · intro e he hf γ h
    obtain ⟨v, -, e', -, hf', -⟩ := h
    exact absurd hf' (by simp)
  · intro e he _
    exact hL'card e he
  · intro x γ
    have heq : RoundCore.uncoloured 𝓗 (fun _ => (none : Option (Fin c))) = 𝓗 := by
      ext e
      simp [RoundCore.uncoloured]
    rw [heq]
    have hinj : Function.Injective
        (fun z : {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L' (e : Set (Fin n))} =>
          (⟨z.1, z.2.1, hL'sub (z.1 : Set (Fin n)) z.1.2 z.2.2⟩ :
            {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e})) := by
      intro a b hab
      exact Subtype.ext (congrArg (fun w => (w.1 : 𝓗)) hab)
    have h1 : Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L' (e : Set (Fin n))}
        ≤ Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} :=
      Nat.card_le_card_of_injective _ hinj
    have h2 : ((Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L' (e : Set (Fin n))} : ℕ) : ℝ)
        ≤ ((Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith [h2, hdeg0 x γ]
  · exact hDi0
  · exact Nat.zero_le _
  · push_cast
    linarith [hη0]
  · have hDi0pos : (0 : ℝ) < (it.Di0 : ℝ) := by
      have h : (1 : ℝ) ≤ (it.Di0 : ℝ) := by exact_mod_cast hDi0
      linarith
    rw [div_le_iff₀ hDi0pos]
    linarith [hΛ10]
  · rw [pow_zero, mul_one]
    exact min_le_right _ _
  · exact le_rfl

/-- **Finishing.**  At the end of the iteration the ratio is at least `8 C`, so the residual
list-colouring problem is in the range of `Work.Deep.Kahn.finishing_step`; gluing the partial
colouring with the residual one (`Work.Deep.Kahn.RoundCore.exists_coloring_of_partial`) gives
the colouring of `𝓗` from `L`. -/
lemma finish (it : It) {Dm : ℝ} (hcond : it.Cond Dm) {n c : ℕ}
    (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (L : 𝓗 → Finset (Fin c))
    (hsize : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ it.C)
    (f : Set (Fin n) → Option (Fin c)) (L' : Set (Fin n) → Finset (Fin c)) (Λ D : ℕ)
    (hinv : Inv it 𝓗 L it.T f L' Λ D) :
    ∃ Φ : 𝓗.Coloring (Fin c), ∀ e : 𝓗, Φ.labels e ∈ L e := by
  classical
  obtain ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb, hT8, hεDi0, hΛ10,
    hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩ := hcond
  have hcon : it.Cond Dm := ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb,
    hT8, hεDi0, hΛ10, hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩
  have hD1' : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hinv.hD1
  have hDpos : (0 : ℝ) < (D : ℝ) := by linarith
  -- the ratio has reached `8 C`
  have hρ8 : 8 * (it.C : ℝ) ≤ (Λ : ℝ) / (D : ℝ) := by
    have hDi0pos : (0 : ℝ) < (it.Di0 : ℝ) := by
      have h : (1 : ℝ) ≤ (it.Di0 : ℝ) := by exact_mod_cast hDi0
      linarith
    have hΛ0pos : (0 : ℝ) < (it.Λ0 : ℝ) := by
      have h : (1 : ℝ) ≤ (it.Λ0 : ℝ) := by exact_mod_cast hΛ0
      linarith
    have hρ0 : (1 + it.ε) ≤ it.ρ0 := by
      rw [It.ρ0_eq, le_div_iff₀ hDi0pos]
      exact hεDi0
    have hpow : (8 * (it.C : ℝ)) / (1 + it.ε) ≤ (1 + it.γ₁) ^ it.T := hT8
    have hρ0pos : (0 : ℝ) < it.ρ0 := by rw [It.ρ0_eq]; exact div_pos hΛ0pos hDi0pos
    have hCnn : (0 : ℝ) ≤ (it.C : ℝ) := by positivity
    have hγ1nn : (0 : ℝ) ≤ 1 + it.γ₁ := by rw [It.γ₁_eq]; linarith
    have h1 : 8 * (it.C : ℝ) ≤ it.ρ0 * (1 + it.γ₁) ^ it.T := by
      have h2 : 8 * (it.C : ℝ) = (1 + it.ε) * ((8 * (it.C : ℝ)) / (1 + it.ε)) := by
        field_simp
      rw [h2]
      exact mul_le_mul hρ0 hpow (by positivity) (le_of_lt hρ0pos)
    exact le_trans (le_min le_rfl h1) hinv.hρmin
  have hΛ8 : 8 * (it.C : ℝ) * (D : ℝ) ≤ (Λ : ℝ) := by
    have h := hρ8
    rw [le_div_iff₀ hDpos] at h
    linarith
  -- the residual colouring
  haveI : Fintype (RoundCore.uncoloured 𝓗 f) := (Set.toFinite _).fintype
  have hCpos : (0 : ℝ) < (it.C : ℝ) := by
    have h : (2 : ℝ) ≤ (it.C : ℝ) := by exact_mod_cast hC
    linarith
  obtain ⟨χ, hχ⟩ := finishing_step (RoundCore.uncoloured 𝓗 f)
    (fun e => L' (e : Set (Fin n))) hCpos hDpos
    (fun e => by
      have h := hsize ⟨(e : Set (Fin n)), e.2.1⟩
      exact_mod_cast h)
    (fun x γ => hinv.hdeg x γ)
    (fun e => by
      have h1 : (L' (e : Set (Fin n))).card = Λ := hinv.hcard (e : Set (Fin n)) e.2.1 e.2.2
      rw [h1]
      exact hΛ8)
  -- glue with the partial colouring
  let Ltot : Set (Fin n) → Finset (Fin c) := fun e => if h : e ∈ 𝓗 then L ⟨e, h⟩ else L' e
  have hLtot : ∀ (e : Set (Fin n)) (he : e ∈ 𝓗), Ltot e = L ⟨e, he⟩ := by
    intro e he
    simp only [Ltot, dif_pos he]
  obtain ⟨Φ, hΦ⟩ := RoundCore.exists_coloring_of_partial 𝓗 Ltot L' f
    hinv.hout
    (fun e => by
      by_cases h : e ∈ 𝓗
      · rw [hLtot e h]; exact hinv.hsub e h
      · simp only [Ltot, dif_neg h]
        exact subset_rfl)
    (fun e γ hf => by
      have he : e ∈ 𝓗 := by
        by_contra h
        rw [hinv.hout e h] at hf
        exact absurd hf (by simp)
      rw [hLtot e he]
      exact hinv.hmem e he γ hf)
    hinv.hproper hinv.hexcl χ hχ
  refine ⟨Φ, fun e => ?_⟩
  have h := hΦ e
  rwa [hLtot (e : Set (Fin n)) e.2] at h

/-- **One round of the iteration.**  A state with ratio below `8 C` can be advanced by one
round: the ratio grows by the factor `1 + γ₁` and the colour-degree bound drops by at most the
factor certified by `retention_recurrence`. -/
lemma step (it : It) {Dm : ℝ} (hcond : it.Cond Dm) {n c : ℕ}
    (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (L : 𝓗 → Finset (Fin c))
    (hlin : 𝓗.IsLinear) (hsize : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ it.C)
    (hround : RoundProp it.C it.ε it.η Dm)
    (hγ : it.γ ≤ it.ε / (4 * (it.K : ℝ)))
    (i : ℕ) (f : Set (Fin n) → Option (Fin c)) (L' : Set (Fin n) → Finset (Fin c))
    (Λ D : ℕ) (hinv : Inv it 𝓗 L i f L' Λ D) (hiT : i < it.T)
    (hρlt : (Λ : ℝ) / (D : ℝ) < 8 * (it.C : ℝ)) :
    ∃ (f' : Set (Fin n) → Option (Fin c)) (L'' : Set (Fin n) → Finset (Fin c))
      (Λ' D' : ℕ), Inv it 𝓗 L (i + 1) f' L'' Λ' D' := by
  obtain ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb, hT8, hεDi0, hΛ10,
    hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩ := hcond
  have hcon : it.Cond Dm := ⟨hC, hε0, hε1, hK, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb,
    hT8, hεDi0, hΛ10, hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩
  classical
  have hDlow := hinv.Dlow_le it hcon
  have hratio := hinv.ratio_ge it hcon
  have hD16K := hinv.K_le_D it hcon
  have hlogD := hinv.logD_le it hcon
  have hKlog := hinv.K_le_log_sq it hcon
  have hηD := hinv.etaD_ge_one it hcon
  have hD1 : 1 ≤ D := hinv.hD1
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have h : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    linarith
  have hKpos : (0 : ℝ) < (it.K : ℝ) := by
    have h : (2 : ℝ) ≤ (it.K : ℝ) := by exact_mod_cast hK
    linarith
  have hCpos : (0 : ℝ) < (it.C : ℝ) := by
    have h : (2 : ℝ) ≤ (it.C : ℝ) := by exact_mod_cast hC
    linarith
  have hD32 : (32 : ℝ) ≤ (D : ℝ) := by
    have h : (16 : ℝ) * (it.K : ℝ) ≤ (D : ℝ) := hD16K
    have h2 : (2 : ℝ) ≤ (it.K : ℝ) := by exact_mod_cast hK
    linarith
  have hΛ4 : 4 ≤ Λ := by
    have h : (4 : ℝ) ≤ (Λ : ℝ) := by nlinarith [hratio, hε0, hD32]
    exact_mod_cast h
  have hΛ1 : 1 ≤ Λ := by omega
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := by
    have h : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ1
    linarith
  have hΛgeD : (D : ℝ) ≤ (Λ : ℝ) := by nlinarith [hratio, hε0]
  have hηΛ : 1 ≤ it.η * (Λ : ℝ) :=
    le_trans hηD (mul_le_mul_of_nonneg_left hΛgeD (le_of_lt hη0))
  have hΛ8 : (Λ : ℝ) ≤ 8 * (it.C : ℝ) * (D : ℝ) := by
    rw [div_lt_iff₀ hDpos] at hρlt
    linarith
  have hη_small : it.η ≤ 1 / 16 := by
    have h : it.η * (it.K : ℝ) ≤ 1 / 16 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
      linarith
    have hK1 : (1 : ℝ) ≤ (it.K : ℝ) := by
      have h3 : (2 : ℝ) ≤ (it.K : ℝ) := by exact_mod_cast hK
      linarith
    have h2 : it.η ≤ it.η * (it.K : ℝ) := by nlinarith [hη0, hK1]
    linarith
  have hΛ10D : (Λ : ℝ) ≤ 10 * (it.C : ℝ) * (D : ℝ) := by
    have h := hinv.hρ10
    rw [div_le_iff₀ hDpos] at h
    linarith
  -- the round
  have h𝓗u : RoundCore.uncoloured 𝓗 f ⊆ 𝓗 := fun e he => (RoundCore.mem_uncoloured.mp he).1
  have hlinu : (RoundCore.uncoloured 𝓗 f).IsLinear := Set.Pairwise.mono h𝓗u hlin
  have h9' : ((it.C : ℝ) + (it.K : ℝ) + it.η⁻¹) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) := by
    have hX9 : ((((it.C : ℝ) + (it.K : ℝ) + it.η⁻¹) ^ (9 : ℕ)) : ℝ) ≤ (D : ℝ) :=
      le_trans h9 hDlow
    have h2 := Real.rpow_le_rpow (by positivity) hX9 (by norm_num : (0 : ℝ) ≤ 1 / 9)
    rwa [rpow_nine_inv _ (by positivity)] at h2
  obtain ⟨𝓗₀, hsub₀, φ, RdL, hφmem, hRdLsub, hRdLcard, hRdLavoid, hRdLdeg⟩ :=
    hround n c (RoundCore.uncoloured 𝓗 f) (fun e => L' (e : Set (Fin n))) D Λ it.K
      hD1 hΛ1 hK (by linarith) h16C hlinu
      (fun e => hsize ⟨(e : Set (Fin n)), e.2.1⟩)
      (fun e => hinv.hcard (e : Set (Fin n)) e.2.1 e.2.2)
      (fun x γ => by exact_mod_cast hinv.hdeg x γ) hratio hΛ10D (le_trans hDm hDlow) hlogD
      hKlog h9'
  -- the arithmetic of one round
  obtain ⟨hgain1, hslow, hQlo, hQhi⟩ :=
    retention_gain (C := it.C) (D := D) (Λ := Λ) (K := it.K) (ε := it.ε)
      hC hK hD1 hΛ1 hε0 hε1 hratio h16C h2C
  have hQpos : (0 : ℝ) <
      (1 - 1 / (it.K : ℝ)) * retentionU Λ it.C D it.K +
        (1 / (it.K : ℝ)) * (1 - retention Λ it.C D it.K) := by linarith
  have hQhalf : (1 / 2 : ℝ) ≤
      (1 - 1 / (it.K : ℝ)) * retentionU Λ it.C D it.K +
        (1 / (it.K : ℝ)) * (1 - retention Λ it.C D it.K) := by linarith
  have hγrec0 : (0 : ℝ) < it.ε / (4 * (it.K : ℝ)) := by positivity
  have hγrec1 : it.ε / (4 * (it.K : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (it.K : ℝ))]
    nlinarith [hε1, hKpos]
  have hs_le_one : retention Λ it.C D it.K ≤ 1 := by
    have hΛ1' : (1 : ℝ) ≤ Λ := by
      have h : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ1
      linarith
    have hK1' : (1 : ℝ) ≤ (it.K : ℝ) := by exact_mod_cast (show 1 ≤ it.K by omega)
    have hx : (1 / (it.K : ℝ)) / (Λ : ℝ) ≤ 1 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < Λ)]
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (it.K : ℝ))]
      have h2 : (1 : ℝ) * 1 ≤ Λ * (it.K : ℝ) :=
        mul_le_mul hΛ1' hK1' zero_le_one (by linarith)
      simpa using h2
    have hbase0 : (0 : ℝ) ≤ 1 - (1 / (it.K : ℝ)) / (Λ : ℝ) := by linarith
    have hbase1 : 1 - (1 / (it.K : ℝ)) / (Λ : ℝ) ≤ 1 := by
      have hpos : (0 : ℝ) ≤ (1 / (it.K : ℝ)) / (Λ : ℝ) := by positivity
      linarith
    rw [show retention Λ it.C D it.K = (1 - (1 / (it.K : ℝ)) / (Λ : ℝ)) ^ (it.C * D) from rfl]
    exact pow_le_one₀ hbase0 hbase1
  have hgain2 : retention Λ it.C D it.K /
      ((1 - 1 / (it.K : ℝ)) * retentionU Λ it.C D it.K +
        (1 / (it.K : ℝ)) * (1 - retention Λ it.C D it.K)) ≤ 256 / 225 := by
    rw [div_le_iff₀ hQpos]
    have h3 : (225 / 256 : ℝ) * (256 / 225) = 1 := by norm_num
    nlinarith [hs_le_one, hQlo, h3]
  have hQ1' : (1 - 1 / (it.K : ℝ)) * retentionU Λ it.C D it.K +
      (1 / (it.K : ℝ)) * (1 - retention Λ it.C D it.K) ≤ 1 - 1 / (4 * (it.K : ℝ)) := by
    have h : (1 : ℝ) / (4 * (it.K : ℝ)) ≤ (1 : ℝ) / (2 * (it.K : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [hKpos])
    linarith [hQhi]
  have hrec := retention_recurrence (C := it.C) (D := D) (Λ := Λ) (K := it.K)
    (ε := it.ε) (η := it.η) (γ := it.ε / (4 * (it.K : ℝ)))
    hC hK hD1 hΛ4 hε0 hε1 hη0 hγrec0 hγrec1 hratio hΛ8 (by linarith)
    (le_trans h32η hγ) hηΛ hηD hD16K hgain1 hgain2 hslow hQhalf hQ1'
  obtain ⟨hrecΛ1, hrecD1, hrec_ratio, hrec_ratio10, hrec_Dle, hrec_gain, hrec_gain2⟩ := hrec
  -- the new state
  set Λ' : ℕ := ⌊(Λ : ℝ) * retention Λ it.C D it.K - it.η * (Λ : ℝ)⌋₊ with hΛ'def
  set D' : ℕ := ⌈newDeg Λ it.C D it.K + it.η * (D : ℝ)⌉₊ with hD'def
  have hΛ'eq : Λ' = ⌊(Λ : ℝ) * retention Λ it.C D it.K - it.η * (Λ : ℝ)⌋₊ := hΛ'def
  have hD'eq : D' = ⌈newDeg Λ it.C D it.K + it.η * (D : ℝ)⌉₊ := hD'def
  have hΛ'1 : 1 ≤ Λ' := by rw [hΛ'eq]; exact hrecΛ1
  have hD'1 : 1 ≤ D' := by rw [hD'eq]; exact hrecD1
  have hΛ'pos : (0 : ℝ) < (Λ' : ℝ) := by
    have h : (1 : ℝ) ≤ (Λ' : ℝ) := by exact_mod_cast hΛ'1
    linarith
  have hD'pos : (0 : ℝ) < (D' : ℝ) := by
    have h : (1 : ℝ) ≤ (D' : ℝ) := by exact_mod_cast hD'1
    linarith
  -- the new lists
  have hexL : ∀ (e : Set (Fin n)) (h1 : e ∈ RoundCore.uncoloured 𝓗 f) (h2 : e ∉ 𝓗₀),
      ∃ t : Finset (Fin c), t ⊆ RdL ⟨e, ⟨h1, h2⟩⟩ ∧ t.card = Λ' := by
    intro e h1 h2
    refine Finset.exists_subset_card_eq ?_
    have h := hRdLcard ⟨e, ⟨h1, h2⟩⟩
    rw [newLambda] at h
    have h2' : ((Λ' : ℕ) : ℝ) ≤ ((RdL ⟨e, ⟨h1, h2⟩⟩).card : ℝ) := by
      have hfl : ((Λ' : ℕ) : ℝ) ≤ (Λ : ℝ) * retention Λ it.C D it.K - it.η * (Λ : ℝ) := by
        rw [hΛ'eq]
        refine Nat.floor_le ?_
        nlinarith [hslow, hΛpos, hη_small]
      linarith
    exact_mod_cast h2'
  let f' : Set (Fin n) → Option (Fin c) := fun e =>
    if h : e ∈ 𝓗₀ then some (φ.labels ⟨e, h⟩) else f e
  let Lq : Set (Fin n) → Finset (Fin c) := fun e =>
    if h1 : e ∈ RoundCore.uncoloured 𝓗 f then
      if h2 : e ∈ 𝓗₀ then L' e else Classical.choose (hexL e h1 h2)
    else L' e
  have hf'none : ∀ e, f' e = none ↔ (e ∉ 𝓗₀ ∧ f e = none) := by
    intro e
    constructor
    · intro h
      have h2 : e ∉ 𝓗₀ := by
        intro hc
        rw [show f' e = some (φ.labels ⟨e, hc⟩) from by simp only [f', dif_pos hc]] at h
        exact absurd h (by simp)
      exact ⟨h2, by simpa only [f', dif_neg h2] using h⟩
    · rintro ⟨h2, hf⟩
      simp only [f', dif_neg h2, hf]
  have hLq_le : ∀ (e : Set (Fin n)) (h1 : e ∈ RoundCore.uncoloured 𝓗 f) (h2 : e ∉ 𝓗₀),
      Lq e ⊆ RdL ⟨e, ⟨h1, h2⟩⟩ := by
    intro e h1 h2
    have h3 : e ∉ 𝓗₀ := h2
    intro γ hγ
    have h4 : γ ∈ Classical.choose (hexL e h1 h2) := by
      have h5 : γ ∈ Lq e := hγ
      rwa [show Lq e = Classical.choose (hexL e h1 h2) from by
        simp only [Lq, dif_pos h1, dif_neg h3]] at h5
    exact (Classical.choose_spec (hexL e h1 h2)).1 h4
  refine ⟨f', Lq, Λ', D', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `hout`
    intro e he
    have he2 : e ∉ 𝓗₀ := fun h => he (h𝓗u (hsub₀ h))
    simp only [f', dif_neg he2]
    exact hinv.hout e he
  · -- `hsub`
    intro e he
    by_cases h1 : e ∈ RoundCore.uncoloured 𝓗 f
    · by_cases h2 : e ∈ 𝓗₀
      · simp only [Lq, dif_pos h1, dif_pos h2]
        exact hinv.hsub e he
      · simp only [Lq, dif_pos h1, dif_neg h2]
        intro γ hγ
        exact hinv.hsub e he (hRdLsub ⟨e, ⟨h1, h2⟩⟩ ((Classical.choose_spec (hexL e h1 h2)).1 hγ))
    · simp only [Lq, dif_neg h1]
      exact hinv.hsub e he
  · -- `hmem`
    intro e he γ hf
    by_cases h2 : e ∈ 𝓗₀
    · have hγ : γ = φ.labels ⟨e, h2⟩ := by
        have h5 := hf
        rw [show f' e = some (φ.labels ⟨e, h2⟩) from by simp only [f', dif_pos h2]] at h5
        exact (Option.some.inj h5).symm
      rw [hγ]
      exact hinv.hsub e he (hφmem ⟨e, h2⟩)
    · have h5 : f e = some γ := by simpa only [f', dif_neg h2] using hf
      exact hinv.hmem e he γ h5
  · -- `hproper`
    intro e₁ e₂ γ₁ γ₂ h1 h2 hne hnon
    by_cases hc₁ : e₁ ∈ 𝓗₀
    · by_cases hc₂ : e₂ ∈ 𝓗₀
      · have hγ₁ : γ₁ = φ.labels ⟨e₁, hc₁⟩ := by
          have h5 := h1
          rw [show f' e₁ = some (φ.labels ⟨e₁, hc₁⟩) from by simp only [f', dif_pos hc₁]] at h5
          exact (Option.some.inj h5).symm
        have hγ₂ : γ₂ = φ.labels ⟨e₂, hc₂⟩ := by
          have h5 := h2
          rw [show f' e₂ = some (φ.labels ⟨e₂, hc₂⟩) from by simp only [f', dif_pos hc₂]] at h5
          exact (Option.some.inj h5).symm
        rw [hγ₁, hγ₂]
        exact φ.isColoring ⟨e₁, hc₁⟩ ⟨e₂, hc₂⟩
          (fun hEq => hne (by simpa using congrArg (fun z : 𝓗₀ => (z : Set (Fin n))) hEq))
          (by simpa using hnon)
      · have hγ₁ : γ₁ = φ.labels ⟨e₁, hc₁⟩ := by
          have h5 := h1
          rw [show f' e₁ = some (φ.labels ⟨e₁, hc₁⟩) from by simp only [f', dif_pos hc₁]] at h5
          exact (Option.some.inj h5).symm
        have hf₂ : f e₂ = some γ₂ := by simpa only [f', dif_neg hc₂] using h2
        have he₂ : e₂ ∈ 𝓗 := by
          by_contra hmem
          rw [hinv.hout e₂ hmem] at hf₂
          exact absurd hf₂ (by simp)
        have he₁ : e₁ ∈ 𝓗 := h𝓗u (hsub₀ hc₁)
        have hnone₁ : f e₁ = none := (RoundCore.mem_uncoloured.mp (hsub₀ hc₁)).2
        obtain ⟨v, hv₁, hv₂⟩ := hnon
        have hexcl₁ := hinv.hexcl e₁ he₁ hnone₁ γ₂ ⟨v, hv₁, e₂, he₂, hf₂, hv₂⟩
        rw [hγ₁]
        exact fun hcon => hexcl₁ (hcon ▸ hφmem ⟨e₁, hc₁⟩)
    · have hf₁ : f e₁ = some γ₁ := by simpa only [f', dif_neg hc₁] using h1
      by_cases hc₂ : e₂ ∈ 𝓗₀
      · have hγ₂ : γ₂ = φ.labels ⟨e₂, hc₂⟩ := by
          have h5 := h2
          rw [show f' e₂ = some (φ.labels ⟨e₂, hc₂⟩) from by simp only [f', dif_pos hc₂]] at h5
          exact (Option.some.inj h5).symm
        have he₁ : e₁ ∈ 𝓗 := by
          by_contra hmem
          rw [hinv.hout e₁ hmem] at hf₁
          exact absurd hf₁ (by simp)
        have he₂ : e₂ ∈ 𝓗 := h𝓗u (hsub₀ hc₂)
        have hnone₂ : f e₂ = none := (RoundCore.mem_uncoloured.mp (hsub₀ hc₂)).2
        obtain ⟨v, hv₁, hv₂⟩ := hnon
        have hexcl₂ := hinv.hexcl e₂ he₂ hnone₂ γ₁ ⟨v, hv₂, e₁, he₁, hf₁, hv₁⟩
        rw [hγ₂]
        exact fun hcon => hexcl₂ (hcon.symm ▸ hφmem ⟨e₂, hc₂⟩)
      · exact hinv.hproper e₁ e₂ γ₁ γ₂ hf₁ (by simpa only [f', dif_neg hc₂] using h2) hne hnon
  · -- `hexcl`
    intro e he hf γ hex'
    have h2 : e ∉ 𝓗₀ := fun hc => by
      rw [show f' e = some (φ.labels ⟨e, hc⟩) from by simp only [f', dif_pos hc]] at hf
      exact absurd hf (by simp)
    have hfe : f e = none := by simpa only [f', dif_neg h2] using hf
    have h1 : e ∈ RoundCore.uncoloured 𝓗 f := RoundCore.mem_uncoloured.mpr ⟨he, hfe⟩
    obtain ⟨v, hv, e', he', hf', hv'⟩ := hex'
    by_cases hc' : e' ∈ 𝓗₀
    · have hγ : γ = φ.labels ⟨e', hc'⟩ := by
        have h5 := hf'
        rw [show f' e' = some (φ.labels ⟨e', hc'⟩) from by simp only [f', dif_pos hc']] at h5
        exact (Option.some.inj h5).symm
      intro hmem
      have hmem' : γ ∈ RdL ⟨e, ⟨h1, h2⟩⟩ := hLq_le e h1 h2 hmem
      rw [hγ] at hmem'
      exact (hRdLavoid ⟨e, ⟨h1, h2⟩⟩ ⟨e', hc'⟩ ⟨v, hv', hv⟩) hmem'
    · have hf'' : f e' = some γ := by simpa only [f', dif_neg hc'] using hf'
      have he'' : e' ∈ 𝓗 := by
        by_contra hmem
        rw [hinv.hout e' hmem] at hf''
        exact absurd hf'' (by simp)
      intro hmem
      have hmem' : γ ∈ RdL ⟨e, ⟨h1, h2⟩⟩ := hLq_le e h1 h2 hmem
      exact hinv.hexcl e he hfe γ ⟨v, hv, e', he'', hf'', hv'⟩
        (hRdLsub ⟨e, ⟨h1, h2⟩⟩ hmem')
  · -- `hcard`
    intro e he hf
    obtain ⟨h2, hfe⟩ := (hf'none e).mp hf
    have h1 : e ∈ RoundCore.uncoloured 𝓗 f := RoundCore.mem_uncoloured.mpr ⟨he, hfe⟩
    have hLq : Lq e = Classical.choose (hexL e h1 h2) := by
      simp only [Lq, dif_pos h1, dif_neg h2]
    rw [hLq]
    exact (Classical.choose_spec (hexL e h1 h2)).2
  · -- `hdeg`
    intro x γ
    have heq : RoundCore.uncoloured 𝓗 f' = (RoundCore.uncoloured 𝓗 f) \ 𝓗₀ := by
      ext e
      rw [RoundCore.mem_uncoloured, Set.mem_sdiff]
      exact ⟨fun h => ⟨⟨h.1, (hf'none e).mp h.2 |>.2⟩, (hf'none e).mp h.2 |>.1⟩,
        fun h => ⟨h.1.1, (hf'none e).mpr ⟨h.2, h.1.2⟩⟩⟩
    rw [heq]
    have hinj : Function.Injective
        (fun z : {e : (RoundCore.uncoloured 𝓗 f \ 𝓗₀ : Set (Set (Fin n))) //
            x ∈ (e : Set (Fin n)) ∧ γ ∈ Lq (e : Set (Fin n))} =>
          (⟨z.1, z.2.1, hLq_le (z.1 : Set (Fin n)) z.1.2.1 z.1.2.2 z.2.2⟩ :
            {e : (RoundCore.uncoloured 𝓗 f \ 𝓗₀ : Set (Set (Fin n))) //
              x ∈ (e : Set (Fin n)) ∧ γ ∈ RdL e})) := by
      intro a b hab
      exact Subtype.ext (congrArg (fun w =>
        (w.1 : (RoundCore.uncoloured 𝓗 f \ 𝓗₀ : Set (Set (Fin n))))) hab)
    have h1 : Nat.card {e : (RoundCore.uncoloured 𝓗 f \ 𝓗₀ : Set (Set (Fin n))) //
        x ∈ (e : Set (Fin n)) ∧ γ ∈ Lq (e : Set (Fin n))}
        ≤ Nat.card {e : (RoundCore.uncoloured 𝓗 f \ 𝓗₀ : Set (Set (Fin n))) //
        x ∈ (e : Set (Fin n)) ∧ γ ∈ RdL e} := Nat.card_le_card_of_injective _ hinj
    have h2 : ((Nat.card {e : (RoundCore.uncoloured 𝓗 f \ 𝓗₀ : Set (Set (Fin n))) //
        x ∈ (e : Set (Fin n)) ∧ γ ∈ RdL e} : ℕ) : ℝ) ≤ (D' : ℝ) := by
      have hD' : newDeg Λ it.C D it.K + it.η * (D : ℝ) ≤ (D' : ℝ) := by
        rw [hD'eq]; exact Nat.le_ceil _
      linarith [hRdLdeg x γ]
    have h3 : Nat.card {e : (RoundCore.uncoloured 𝓗 f \ 𝓗₀ : Set (Set (Fin n))) //
        x ∈ (e : Set (Fin n)) ∧ γ ∈ Lq (e : Set (Fin n))} ≤ D' :=
      le_trans h1 (by exact_mod_cast h2)
    exact_mod_cast h3
  · -- `hD1`
    exact hD'1
  · -- `hiT`
    omega
  · -- `hpot`
    have hb0 : (0 : ℝ) ≤ it.b := by
      have h1 : (0 : ℝ) ≤ 32 * (it.C : ℝ) / it.ε := by positivity
      linarith
    have hηs : 8 * it.η ≤ 1 / 2 := by linarith [hη_small]
    have hγ1' : it.ε / (4 * (it.K : ℝ)) ≤ 1 := hγrec1
    have hΛ'mem : (Λ : ℝ) * retention Λ it.C D it.K - 2 * it.η * (Λ : ℝ) ≤ (Λ' : ℝ) := by
      have hf1 : (Λ' : ℝ) ≥ (Λ : ℝ) * retention Λ it.C D it.K - it.η * (Λ : ℝ) - 1 := by
        rw [hΛ'eq]
        have h2 := Nat.lt_floor_add_one ((Λ : ℝ) * retention Λ it.C D it.K - it.η * (Λ : ℝ))
        linarith
      nlinarith [hf1, hηΛ]
    have h1s : 1 - retention Λ it.C D it.K ≤
        (it.C : ℝ) / ((it.K : ℝ) * ((Λ : ℝ) / (D : ℝ))) := by
      have hbern : 1 - retention Λ it.C D it.K ≤
          ((it.C : ℝ) * (D : ℝ)) * ((1 / (it.K : ℝ)) / (Λ : ℝ)) := by
        have hx1 : ((1 / (it.K : ℝ)) / (Λ : ℝ)) ≤ 1 := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Λ : ℝ))]
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (it.K : ℝ))]
          have hL : (1 : ℝ) ≤ Λ := by
            have h : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ1
            linarith
          have hK1 : (1 : ℝ) ≤ (it.K : ℝ) := by exact_mod_cast (show 1 ≤ it.K by omega)
          have h2 : (1 : ℝ) * 1 ≤ Λ * (it.K : ℝ) :=
            mul_le_mul hL hK1 zero_le_one (by linarith [hL])
          simpa using h2
        have hx2 : -2 ≤ -((1 / (it.K : ℝ)) / (Λ : ℝ)) := by linarith
        have h3 := one_add_mul_le_pow hx2 (it.C * D)
        have h4 : (1 : ℝ) + ((it.C * D : ℕ) : ℝ) * (-((1 / (it.K : ℝ)) / (Λ : ℝ)))
            = 1 - ((it.C : ℝ) * (D : ℝ)) * ((1 / (it.K : ℝ)) / (Λ : ℝ)) := by
          push_cast; ring
        rw [h4] at h3
        have h5 : ((1 : ℝ) + -((1 / (it.K : ℝ)) / (Λ : ℝ))) ^ (it.C * D)
            = retention Λ it.C D it.K := by
          rw [show retention Λ it.C D it.K = (1 - (1 / (it.K : ℝ)) / (Λ : ℝ)) ^ (it.C * D)
            from rfl]
          ring_nf
        rw [h5] at h3
        linarith [h3]
      have h6 : ((it.C : ℝ) * (D : ℝ)) * ((1 / (it.K : ℝ)) / (Λ : ℝ))
          = (it.C : ℝ) / ((it.K : ℝ) * ((Λ : ℝ) / (D : ℝ))) := by
        field_simp
      linarith [hbern, h6]
    have hb : 8 * (it.C : ℝ) / ((it.K : ℝ) * (it.ε / (4 * (it.K : ℝ)))) ≤ it.b := by
      have h1 : (it.K : ℝ) * (it.ε / (4 * (it.K : ℝ))) = it.ε / 4 := by
        field_simp
      rw [h1]
      have h2 : 8 * (it.C : ℝ) / (it.ε / 4) = 32 * (it.C : ℝ) / it.ε := by
        field_simp
        ring
      rw [h2]
      linarith
    have hpot' := pot_step (Λ := Λ) (D := D) (Λ' := Λ') (D' := D')
      (s := retention Λ it.C D it.K) (b := it.b) (η := it.η)
      (γ := it.ε / (4 * (it.K : ℝ))) (C := it.C) (K := it.K)
      hΛpos hDpos hΛ'pos hD'pos hslow hη0 hηs hb0 hγrec0 hγrec1 hηΛ hΛ'mem h1s hrec_gain hb
    push_cast
    linarith [hpot', hinv.hpot]
  · -- `hρ10`
    have h := hrec_ratio10
    have hρ : (Λ : ℝ) / (D : ℝ) ≤ 8 * (it.C : ℝ) := le_of_lt hρlt
    linarith [h, hρ]
  · -- `hρmin`
    have hmin := hinv.hρmin
    have hρ' : (1 + (it.ε / (4 * (it.K : ℝ))) / 2) * ((Λ : ℝ) / (D : ℝ)) ≤ (Λ' : ℝ) / (D' : ℝ) :=
      hrec_gain
    have hγ2 : it.γ₁ ≤ (it.ε / (4 * (it.K : ℝ))) / 2 := by
      rw [It.γ₁_eq]; linarith [hγ]
    have hγ1nn : (0 : ℝ) ≤ it.γ₁ := by rw [It.γ₁_eq]; linarith
    have hpowpos : (0 : ℝ) < (1 + it.γ₁) ^ i := by positivity
    rcases min_le_iff.mp hmin with hmin | hmin
    · have h3 : 8 * (it.C : ℝ) ≤ (Λ' : ℝ) / (D' : ℝ) := by
        have h4 : (1 : ℝ) ≤ 1 + (it.ε / (4 * (it.K : ℝ))) / 2 := by linarith [hγrec0]
        nlinarith [hρ', hmin, h4, hCpos]
      exact le_trans (min_le_left _ _) h3
    · have h1 : it.ρ0 * (1 + it.γ₁) ^ i * (1 + it.γ₁)
          ≤ ((Λ : ℝ) / (D : ℝ)) * (1 + it.ε / (4 * (it.K : ℝ)) / 2) := by
        apply mul_le_mul hmin _ _ _
        · linarith [hγ2]
        · linarith [hγ1nn]
        · positivity
      have h2 : it.ρ0 * (1 + it.γ₁) ^ (i + 1) ≤ (Λ' : ℝ) / (D' : ℝ) := by
        rw [pow_succ]
        linarith [h1, hρ']
      exact le_trans (min_le_right _ _) h2
  · -- `hDle`
    have h := hrec_Dle
    rw [hD'eq] at h
    linarith [h, hinv.hDle]


/-! ## 4.  The reduction -/


/-- **The initial state for the concrete parameters `mkIt`.**  This is `init` with the
numerical facts about `mkIt` discharged; it is kept separate so that the (large) context of
the main theorem is not duplicated inside the elaboration of `init`. -/
lemma init_it {n c : ℕ} {r : ℕ} {β : ℝ} {Dk : ℝ} {Dm : ℝ}
    (hεβ : min β 1 ≤ β) (hC : 2 ≤ r)
    (hDk : Real.exp (Real.exp (10 ^ 10 * (1 + (r : ℝ) + (min β 1)⁻¹ + (r : ℝ) * (min β 1)⁻¹)))
      ≤ Dk)
    (hcond : (mkIt r (min β 1) Dk).Cond Dm)
    (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (L : 𝓗 → Finset (Fin c))
    (hmax : ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ Dk)
    (hL : ∀ e : 𝓗, (1 + β) * Dk ≤ ((L e).card : ℝ)) :
    ∃ (f : Set (Fin n) → Option (Fin c)) (L' : Set (Fin n) → Finset (Fin c)) (Λ D : ℕ),
      Inv (mkIt r (min β 1) Dk) 𝓗 L 0 f L' Λ D := by
  classical
  obtain ⟨hC2, hε0, hε1, hK2, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η, h32η, hb, hT8, hεDi0, hΛ10,
    hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩ := hcond
  have hDkpos : (0 : ℝ) < Dk := lt_of_lt_of_le (Real.exp_pos _) hDk
  refine init (mkIt r (min β 1) Dk) ⟨hC2, hε0, hε1, hK2, hη0, hγ0, hDi0, hΛ0, h16C, h2C, h16η,
    h32η, hb, hT8, hεDi0, hΛ10, hlogDi0, hηTb, hDm, h9, hexp, h16K, hηinv⟩ 𝓗 L ?_ ?_
  · intro e
    have h4 : (1 + β) * Dk ≤ ((L e).card : ℝ) := hL e
    have h3 : (1 + min β 1) * Dk ≤ ((L e).card : ℝ) := by nlinarith [h4, hεβ, hDkpos]
    have h5 : (⌊Dk⌋₊ : ℝ) ≤ Dk := Nat.floor_le hDkpos.le
    have h2 : (1 + min β 1) * (⌊Dk⌋₊ : ℝ) ≤ ((L e).card : ℝ) := by
      nlinarith [h3, h5, hDkpos, hε0]
    rw [mkIt_Λ0]
    exact Nat.cast_le.mpr (Nat.ceil_le.mpr h2)
  · intro x γ
    have hinj : Function.Injective
        (fun z : {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} =>
          (⟨z.1, z.2.1⟩ : {e : 𝓗 // x ∈ (e : Set (Fin n))})) :=
      fun a b hab => Subtype.ext (congrArg (fun w => (w.1 : 𝓗)) hab)
    have h1 : Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} ≤
        Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n))} :=
      Nat.card_le_card_of_injective _ hinj
    rw [show Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n))} = hypergraphDegree 𝓗 x from rfl] at h1
    have h3 : hypergraphMaxDegree 𝓗 ≤ ⌊Dk⌋₊ := Nat.le_floor hmax
    rw [mkIt_Di0]
    exact Nat.cast_le.mpr (le_trans h1 (hypergraphDegree_le_maxDegree 𝓗 x |>.trans h3))

/-- **The iteration.**  From a state at time `0` and the one-round step, produce a state at
time `T`. -/
lemma iterate (it : It) {Dm : ℝ} (hcond : it.Cond Dm) {n c : ℕ}
    (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (L : 𝓗 → Finset (Fin c))
    (hlin : 𝓗.IsLinear) (hsize : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ it.C)
    (hround : RoundProp it.C it.ε it.η Dm)
    (hγ : it.γ ≤ it.ε / (4 * (it.K : ℝ)))
    (hinit : ∃ (f : Set (Fin n) → Option (Fin c)) (L' : Set (Fin n) → Finset (Fin c))
      (Λ D : ℕ), Inv it 𝓗 L 0 f L' Λ D) :
    ∃ (f : Set (Fin n) → Option (Fin c)) (L' : Set (Fin n) → Finset (Fin c)) (Λ D : ℕ),
      Inv it 𝓗 L it.T f L' Λ D := by
  have hη0 : (0 : ℝ) < it.η := hcond.2.2.2.2.1
  have hmain : ∀ i ≤ it.T, ∃ (f : Set (Fin n) → Option (Fin c))
      (L' : Set (Fin n) → Finset (Fin c)) (Λ D : ℕ), Inv it 𝓗 L i f L' Λ D := by
    intro i
    induction i with
    | zero => intro _; exact hinit
    | succ i ih =>
        intro hi
        obtain ⟨f, L', Λ, D, hinv⟩ := ih (by omega)
        by_cases hρ : (Λ : ℝ) / (D : ℝ) < 8 * (it.C : ℝ)
        · obtain ⟨f', L'', Λ', D', hinv'⟩ :=
            step it hcond 𝓗 L hlin hsize hround hγ i f L' Λ D hinv (by omega) hρ
          exact ⟨f', L'', Λ', D', hinv'⟩
        · push_neg at hρ
          refine ⟨f, L', Λ, D, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact hinv.hout
          · exact hinv.hsub
          · exact hinv.hmem
          · exact hinv.hproper
          · exact hinv.hexcl
          · exact hinv.hcard
          · exact hinv.hdeg
          · exact hinv.hD1
          · exact hi
          · have hη' : (0 : ℝ) ≤ 8 * it.η := by positivity
            push_cast
            linarith [hinv.hpot, hη']
          · exact hinv.hρ10
          · exact le_trans (min_le_left _ _) hρ
          · exact hinv.hDle
  exact hmain it.T le_rfl

/-- **Kahn's theorem for hypergraphs with edges of size at least two, from the colour-degree
one-round nibble step.** -/
theorem kahnCore_of_roundStepB (h : Work.Deep.Kahn.RoundStepStatement) : ErdosFaberLovaszConjecture.KahnCoreStatement := by
  intro β hβ r hr
  set ε : ℝ := min β 1 with hεdef
  have hε0 : 0 < ε := lt_min hβ zero_lt_one
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεβ : ε ≤ β := min_le_left _ _
  have hC : 2 ≤ r := hr
  refine ⟨Real.exp (Real.exp (10 ^ 10 * (1 + (r : ℝ) + ε⁻¹ + (r : ℝ) * ε⁻¹))),
    Real.exp_pos _, ?_⟩
  intro Dk hDk n 𝓗 hlin hmax hsize2 hsize c hc L hL
  classical
  -- the parameters of the iteration
  set it : It := mkIt r ε Dk with hitdef
  have hη0 : 0 < it.η := by
    rw [hitdef, mkIt_η]
    apply div_pos hε0
    have h2 : 0 < mkK r ε Dk := by unfold mkK; positivity
    positivity
  -- the one-round step, with its threshold
  obtain ⟨Dm, hDm0, hDmle, hround⟩ :=
    h r hC it.ε it.η (by rw [hitdef, mkIt_ε]; exact hε0) hη0
  have hround' : RoundProp it.C it.ε it.η Dm := hround
  have hγ : it.γ ≤ it.ε / (4 * (it.K : ℝ)) := le_of_eq rfl
  -- the numerical conditions
  have hcond : it.Cond Dm := by
    have hDm' : Dm ≤ ((r : ℝ) + it.η⁻¹ + it.ε⁻¹ + 1) ^ (1000 : ℕ) + 10 ^ 1000 := by
      rw [hitdef, mkIt_ε]
      exact hDmle
    exact mkIt_cond r hC ε hε0 hε1 Dk hDk Dm hDm'
  -- the initial state
  have hinit : ∃ (f : Set (Fin n) → Option (Fin c)) (L' : Set (Fin n) → Finset (Fin c))
      (Λ D : ℕ), Inv it 𝓗 L 0 f L' Λ D :=
    init_it (n := n) (c := c) (r := r) (β := β) (Dk := Dk) (Dm := Dm)
      hεβ hC hDk hcond 𝓗 L hmax hL
  have hsizeIt : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ it.C := by
    intro e
    have h1 : ((edgeSize (e : Set (Fin n)) : ℕ) : ℝ) ≤ (it.C : ℝ) := by
      rw [hitdef, mkIt_C]; exact hsize e
    exact_mod_cast h1
  -- the iteration, and the finishing step
  obtain ⟨f, L', Λ, D, hinv⟩ := iterate it hcond 𝓗 L hlin hsizeIt hround' hγ hinit
  exact finish it hcond 𝓗 L hsizeIt f L' Λ D hinv

end

end Work.Deep.Kahn
