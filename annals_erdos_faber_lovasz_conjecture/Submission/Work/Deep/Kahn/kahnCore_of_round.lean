import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Nibble
import Submission.Work.Deep.Kahn.listColorable_of_card_gt_sum_degree

/-!
# Kahn's theorem from the one-round nibble step

`kahnCore_of_round`: iterate the one-round step `KahnRoundStatement`
(`Nibble.lean`) while the slack `(list size)/(degree)` grows by the factor
`(1-ψ)/(1-θ) > 1` at every round; a bounded number `k*` of rounds brings the
hypergraph into the range of the greedy list-colouring bound
(`listColorable_of_card_gt_sum_degree`).

This file carries the bookkeeping of the iteration: the partial colouring
(`f : Set (Fin n) → Option (Fin c)`), the current lists `L'`, and the
invariant `RoundInv` relating them to the input `𝓗`, `L`:

* every colour of `f` lies in the original list (`mem`), and `f` is proper on
  its domain (`proper`);
* the maximum degree of the uncoloured part has dropped by `(1-θ)^i` (`deg`);
* the current list of every uncoloured edge still has size at least
  `(1+β)D(1 - (ψ/θ)(1 - (1-θ)^i))` (`list_card`);
* every colour used at a vertex of an uncoloured edge is already missing from
  its current list (`excl`) --- this is what makes the round colourings of
  different rounds compatible, and it is inherited because each round loses at
  most a `ψ`-fraction of every list.

At the end (`k*` rounds) the greedy bound applies, and `glueLabel` reassembles
the partial colouring with the colouring of the uncoloured remainder.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

-- The auxiliary vocabulary of the iteration, kept in its own namespace so that
-- it cannot collide with the vocabulary of a proof of `KahnRoundStatement` itself.
namespace RoundCore

/-- The edges of `𝓗` not yet coloured by the partial colouring `f`. -/
def uncoloured {n c : ℕ} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (f : Set (Fin n) → Option (Fin c)) : ErdosFaberLovaszConjecture.Hypergraph (Fin n) :=
  {e | e ∈ 𝓗 ∧ f e = none}

lemma mem_uncoloured {n c : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {f : Set (Fin n) → Option (Fin c)} {e : Set (Fin n)} :
    e ∈ uncoloured 𝓗 f ↔ e ∈ 𝓗 ∧ f e = none := Iff.rfl

lemma maxDegree_le_of_forall {n : ℕ} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ v, ((hypergraphDegree 𝓗 v : ℕ) : ℝ) ≤ B) :
    ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ B := by
  have h' : hypergraphMaxDegree 𝓗 ≤ ⌊B⌋₊ := by
    rw [hypergraphMaxDegree]
    exact Finset.sup_le (fun v _ => Nat.le_floor (h v))
  calc ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ (⌊B⌋₊ : ℝ) := by exact_mod_cast h'
    _ ≤ B := Nat.floor_le hB

lemma list_card_lower {β θ ψ D : ℝ} (hθ0 : 0 < θ) (hψθ : ψ ≤ θ) (hθ1 : θ ≤ 1)
    (hβ : 0 ≤ β) (hD : 0 ≤ D) (i : ℕ) :
    (1 + β) * ((1 - θ)^i * D) ≤ (1 + β) * D * (1 - (ψ / θ) * (1 - (1 - θ)^i)) := by
  have hθnn : 0 ≤ 1 - θ := by linarith
  have ha1 : (1 - θ)^i ≤ 1 := pow_le_pow_of_le_one hθnn (by linarith) (Nat.zero_le i)
  have hs1 : ψ / θ ≤ 1 := (div_le_one hθ0).mpr hψθ
  have hkey : (1 - θ)^i ≤ 1 - (ψ / θ) * (1 - (1 - θ)^i) := by
    have h : (1 - θ)^i * (1 - ψ / θ) ≤ 1 * (1 - ψ / θ) :=
      mul_le_mul_of_nonneg_right ha1 (by linarith)
    nlinarith [h]
  calc (1 + β) * ((1 - θ)^i * D) = (1 + β) * D * (1 - θ)^i := by ring
    _ ≤ (1 + β) * D * (1 - (ψ / θ) * (1 - (1 - θ)^i)) :=
        mul_le_mul_of_nonneg_left hkey (mul_nonneg (by linarith) hD)

lemma lostColours_subset {n c : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    (𝓗₀ : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (hsub : ∀ e ∈ 𝓗₀, e ∈ 𝓗) (φ : 𝓗₀.Coloring (Fin c)) (L : 𝓗 → Finset (Fin c)) (e : 𝓗) :
    lostColours 𝓗₀ hsub φ L e ⊆ L e := by
  classical
  intro γ hγ
  rw [lostColours] at hγ
  exact (Finset.mem_filter.mp hγ).1

/-- The invariant maintained by the iteration. -/
structure RoundInv {n c : ℕ} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (Ltot : Set (Fin n) → Finset (Fin c)) (β θ ψ D : ℝ) (i : ℕ)
    (f : Set (Fin n) → Option (Fin c)) (L' : Set (Fin n) → Finset (Fin c)) : Prop where
  out : ∀ e, e ∉ 𝓗 → f e = none
  list_sub : ∀ e, L' e ⊆ Ltot e
  mem : ∀ e γ, f e = some γ → γ ∈ Ltot e
  proper : ∀ e₁ e₂ γ₁ γ₂, f e₁ = some γ₁ → f e₂ = some γ₂ → e₁ ≠ e₂ →
    (e₁ ∩ e₂ : Set (Fin n)).Nonempty → γ₁ ≠ γ₂
  deg : ((hypergraphMaxDegree (uncoloured 𝓗 f) : ℕ) : ℝ) ≤ (1 - θ)^i * D
  list_card : ∀ e, e ∈ 𝓗 → f e = none →
    (1 + β) * D * (1 - (ψ / θ) * (1 - (1 - θ)^i)) ≤ ((L' e).card : ℝ)
  excl : ∀ e, e ∈ 𝓗 → f e = none → ∀ γ : Fin c,
    (∃ v ∈ e, ∃ e' ∈ 𝓗, f e' = some γ ∧ v ∈ e') → γ ∉ L' e

/-- Gluing a partial colouring `f` with a colouring `χ` of the uncoloured part. -/
noncomputable def glueLabel {n c : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    (f : Set (Fin n) → Option (Fin c))
    (χ : ErdosFaberLovaszConjecture.Hypergraph.Coloring (Fin c) {x | x ∈ 𝓗 ∧ f x = none})
    (e : 𝓗) : Fin c :=
  match h : f (e : Set (Fin n)) with
  | none => χ.labels ⟨(e : Set (Fin n)), e.2, h⟩
  | some γ => γ

lemma glueLabel_none {n c : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {f : Set (Fin n) → Option (Fin c)}
    {χ : ErdosFaberLovaszConjecture.Hypergraph.Coloring (Fin c) {x | x ∈ 𝓗 ∧ f x = none}}
    {e : 𝓗} (h : f (e : Set (Fin n)) = none) :
    glueLabel f χ e = χ.labels ⟨(e : Set (Fin n)), e.2, h⟩ := by
  rw [glueLabel]
  split
  · rfl
  · next he => exact absurd (he.symm.trans h) (by simp)

lemma glueLabel_some {n c : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {f : Set (Fin n) → Option (Fin c)}
    {χ : ErdosFaberLovaszConjecture.Hypergraph.Coloring (Fin c) {x | x ∈ 𝓗 ∧ f x = none}}
    {e : 𝓗} {γ : Fin c} (h : f (e : Set (Fin n)) = some γ) :
    glueLabel f χ e = γ := by
  rw [glueLabel]
  split
  · next he => exact absurd (h.symm.trans he) (by simp)
  · next he => exact Option.some.inj (he.symm.trans h)

theorem exists_coloring_of_partial {n c : ℕ}
    (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (L L' : Set (Fin n) → Finset (Fin c)) (f : Set (Fin n) → Option (Fin c))
    (hout : ∀ e, e ∉ 𝓗 → f e = none)
    (hsub : ∀ e, L' e ⊆ L e)
    (hmem : ∀ e γ, f e = some γ → γ ∈ L e)
    (hproper : ∀ e₁ e₂ γ₁ γ₂, f e₁ = some γ₁ → f e₂ = some γ₂ → e₁ ≠ e₂ →
      (e₁ ∩ e₂ : Set (Fin n)).Nonempty → γ₁ ≠ γ₂)
    (hexcl : ∀ e, e ∈ 𝓗 → f e = none → ∀ γ : Fin c,
      (∃ v ∈ e, ∃ e' ∈ 𝓗, f e' = some γ ∧ v ∈ e') → γ ∉ L' e)
    (χ : ErdosFaberLovaszConjecture.Hypergraph.Coloring (Fin c) {x | x ∈ 𝓗 ∧ f x = none})
    (hχ : ∀ e : {x | x ∈ 𝓗 ∧ f x = none}, χ.labels e ∈ L' (e : Set (Fin n))) :
    ∃ Φ : ErdosFaberLovaszConjecture.Hypergraph.Coloring (Fin c) 𝓗,
      ∀ e : 𝓗, Φ.labels e ∈ L (e : Set (Fin n)) := by
  classical
  have hsetne : ∀ e₁ e₂ : 𝓗, e₁ ≠ e₂ → (e₁ : Set (Fin n)) ≠ (e₂ : Set (Fin n)) :=
    fun e₁ e₂ h hEq => h (Subtype.ext hEq)
  refine ⟨{ labels := glueLabel f χ, isColoring := ?_ }, ?_⟩
  · intro e₁ e₂ hne hint
    obtain ⟨v, hv1, hv2⟩ := hint
    by_cases h1 : f (e₁ : Set (Fin n)) = none
    · by_cases h2 : f (e₂ : Set (Fin n)) = none
      · rw [glueLabel_none h1, glueLabel_none h2]
        exact χ.isColoring ⟨(e₁ : Set (Fin n)), e₁.2, h1⟩ ⟨(e₂ : Set (Fin n)), e₂.2, h2⟩
          (fun hEq => hne (Subtype.ext (congrArg (fun x : {x | x ∈ 𝓗 ∧ f x = none} =>
            (x : Set (Fin n))) hEq))) ⟨v, hv1, hv2⟩
      · rw [glueLabel_none h1]
        cases hf2 : f (e₂ : Set (Fin n)) with
        | none => exact absurd hf2 h2
        | some γ₂ =>
            rw [glueLabel_some hf2]
            intro hcon
            have hmem' := hχ ⟨(e₁ : Set (Fin n)), e₁.2, h1⟩
            exact hexcl _ e₁.2 h1 γ₂ ⟨v, hv1, e₂, e₂.2, hf2, hv2⟩ (hcon ▸ hmem')
    · by_cases h2 : f (e₂ : Set (Fin n)) = none
      · rw [glueLabel_none h2]
        cases hf1 : f (e₁ : Set (Fin n)) with
        | none => exact absurd hf1 h1
        | some γ₁ =>
            rw [glueLabel_some hf1]
            intro hcon
            have hmem' := hχ ⟨(e₂ : Set (Fin n)), e₂.2, h2⟩
            exact hexcl _ e₂.2 h2 γ₁ ⟨v, hv2, e₁, e₁.2, hf1, hv1⟩ (hcon.symm ▸ hmem')
      · cases hf1 : f (e₁ : Set (Fin n)) with
        | none => exact absurd hf1 h1
        | some γ₁ =>
            cases hf2 : f (e₂ : Set (Fin n)) with
            | none => exact absurd hf2 h2
            | some γ₂ =>
                rw [glueLabel_some hf1, glueLabel_some hf2]
                exact hproper _ _ _ _ hf1 hf2 (hsetne e₁ e₂ hne) ⟨v, hv1, hv2⟩
  · intro e
    by_cases h : f (e : Set (Fin n)) = none
    · show glueLabel f χ e ∈ L (e : Set (Fin n))
      rw [glueLabel_none h]
      exact hsub _ (hχ ⟨(e : Set (Fin n)), e.2, h⟩)
    · cases hf : f (e : Set (Fin n)) with
      | none => exact absurd hf h
      | some γ =>
          show glueLabel f χ e ∈ L (e : Set (Fin n))
          rw [glueLabel_some hf]
          exact hmem _ _ hf

end RoundCore

open RoundCore

theorem kahnCore_of_round (h : ErdosFaberLovaszConjecture.KahnRoundStatement) :
    ErdosFaberLovaszConjecture.KahnCoreStatement := by
  classical
  intro β hβ r hr
  obtain ⟨θ, ψ, hψpos, hψθ, hθ1, D₀, hD₀pos, hround⟩ := h β hβ r hr
  have hθpos : 0 < θ := lt_trans hψpos hψθ
  have hθnn : 0 ≤ 1 - θ := by linarith
  have hεpos : 0 < 1 - ψ / θ := by
    have hlt : ψ / θ < 1 := (div_lt_one hθpos).mpr hψθ
    linarith
  have hApos : 0 < (1 + β) * (1 - ψ / θ) := mul_pos (by linarith) hεpos
  obtain ⟨kstar, hkstar⟩ : ∃ k : ℕ, (r : ℝ) * (1 - θ)^k ≤ (1 + β) * (1 - ψ / θ) / 2 := by
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hthr : 0 < (1 + β) * (1 - ψ / θ) / (4 * (r : ℝ)) := by positivity
    have htend : Filter.Tendsto (fun k : ℕ => (1 - θ)^k) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hθnn (by linarith)
    have hev : ∀ᶠ k : ℕ in Filter.atTop,
        (1 - θ)^k < (1 + β) * (1 - ψ / θ) / (4 * (r : ℝ)) :=
      (tendsto_order.1 htend).2 _ hthr
    obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp hev
    refine ⟨k₀, ?_⟩
    have h1 : (r : ℝ) * (1 - θ)^k₀ < (1 + β) * (1 - ψ / θ) / 4 := by
      have hh := mul_lt_mul_of_pos_left (hk₀ k₀ le_rfl) hr0
      have h2 : (r : ℝ) * ((1 + β) * (1 - ψ / θ) / (4 * (r : ℝ)))
          = (1 + β) * (1 - ψ / θ) / 4 := by field_simp
      rwa [h2] at hh
    linarith
  refine ⟨D₀ / (1 - θ)^kstar, div_pos hD₀pos (pow_pos (by linarith) _), ?_⟩
  intro D hD n 𝓗 hlin hdeg hsize2 hsize c _hc L hL
  have hDpos : 0 < D := lt_of_lt_of_le (div_pos hD₀pos (pow_pos (by linarith) kstar)) hD
  have hDnn : 0 ≤ D := le_of_lt hDpos
  have hDpow : D₀ ≤ (1 - θ)^kstar * D := by
    have h := (div_le_iff₀ (pow_pos (by linarith : (0:ℝ) < 1 - θ) kstar)).mp hD
    linarith
  have hDmono : ∀ i, i ≤ kstar → D₀ ≤ (1 - θ)^i * D := by
    intro i hi
    have h2 : (1 - θ)^kstar ≤ (1 - θ)^i := pow_le_pow_of_le_one hθnn (by linarith) hi
    exact le_trans hDpow (mul_le_mul_of_nonneg_right h2 hDnn)
  let Ltot : Set (Fin n) → Finset (Fin c) := fun e => if h : e ∈ 𝓗 then L ⟨e, h⟩ else ∅
  have hLtot : ∀ (e : Set (Fin n)) (he : e ∈ 𝓗), Ltot e = L ⟨e, he⟩ := by
    intro e he
    simp only [Ltot]
    rw [dif_pos he]
  have hmain : ∀ i, i ≤ kstar → ∃ f L', RoundInv 𝓗 Ltot β θ ψ D i f L' := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨fun _ => (none : Option (Fin c)), Ltot, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro e _
        rfl
      · intro e
        exact subset_rfl
      · intro e γ hf
        exact absurd hf (by simp)
      · intro e₁ e₂ γ₁ γ₂ h₁
        exact absurd h₁ (by simp)
      · have hEq : uncoloured 𝓗 (fun _ => (none : Option (Fin c))) = 𝓗 := by
          ext e
          simp [uncoloured]
        rw [hEq, pow_zero, one_mul]
        exact hdeg
      · intro e he _
        rw [pow_zero]
        have hh := hL ⟨e, he⟩
        rw [hLtot e he]
        simpa using hh
      · intro e _ _ γ hex
        obtain ⟨v, hv, e', he', hf', hv'⟩ := hex
        exact absurd hf' (by simp)
    | succ i ih =>
      intro hi
      obtain ⟨f, Lp, hinv⟩ := ih (by omega)
      have hDi : D₀ ≤ (1 - θ)^i * D := hDmono i (by omega)
      have hlin_i : (uncoloured 𝓗 f).IsLinear := hlin.mono (fun e he => (mem_uncoloured.mp he).1)
      have hsize2_i : ∀ e : uncoloured 𝓗 f, 2 ≤ edgeSize (e : Set (Fin n)) :=
        fun e => hsize2 ⟨(e : Set (Fin n)), (mem_uncoloured.mp e.2).1⟩
      have hsize_i : ∀ e : uncoloured 𝓗 f, (edgeSize (e : Set (Fin n)) : ℝ) ≤ (r : ℝ) :=
        fun e => hsize ⟨(e : Set (Fin n)), (mem_uncoloured.mp e.2).1⟩
      let Li : uncoloured 𝓗 f → Finset (Fin c) := fun e => Lp (e : Set (Fin n))
      have hLi : ∀ e : uncoloured 𝓗 f, (1 + β) * ((1 - θ)^i * D) ≤ ((Li e).card : ℝ) := by
        intro e
        refine le_trans ?_ (hinv.list_card (e : Set (Fin n)) (mem_uncoloured.mp e.2).1
          (mem_uncoloured.mp e.2).2)
        exact list_card_lower hθpos (le_of_lt hψθ) (le_of_lt hθ1) (le_of_lt hβ) hDnn i
      obtain ⟨𝓖, hsub₀, φ, hφmem, hφprog, hφloss⟩ :=
        hround ((1 - θ)^i * D) hDi n (uncoloured 𝓗 f) hlin_i hinv.deg hsize2_i hsize_i c Li hLi
      let f' : Set (Fin n) → Option (Fin c) :=
        fun e => if h : e ∈ 𝓖 then some (φ.labels ⟨e, h⟩) else f e
      let Lq : Set (Fin n) → Finset (Fin c) :=
        fun e => if h : e ∈ uncoloured 𝓗 f then
            Lp e \ lostColours 𝓖 hsub₀ φ Li ⟨e, h⟩ else Lp e
      refine ⟨f', Lq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro e he
        show f' e = none
        simp only [f']
        by_cases h : e ∈ 𝓖
        · rw [dif_pos h]
          exact absurd (mem_uncoloured.mp (hsub₀ e h)).1 he
        · rw [dif_neg h]
          exact hinv.out e he
      · intro e
        show Lq e ⊆ Ltot e
        simp only [Lq]
        by_cases h : e ∈ uncoloured 𝓗 f
        · rw [dif_pos h]
          exact fun x hx => hinv.list_sub e (Finset.mem_sdiff.mp hx).1
        · rw [dif_neg h]
          exact hinv.list_sub e
      · intro e γ hf'
        simp only [f'] at hf'
        by_cases h : e ∈ 𝓖
        · rw [dif_pos h] at hf'
          have hγ : γ = φ.labels ⟨e, h⟩ := (Option.some.inj hf').symm
          rw [hγ]
          exact hinv.list_sub e (by simpa [Li] using hφmem ⟨e, h⟩)
        · rw [dif_neg h] at hf'
          exact hinv.mem e γ hf'
      · intro e₁ e₂ γ₁ γ₂ h₁ h₂ hne hnon
        simp only [f'] at h₁ h₂
        by_cases hc₁ : e₁ ∈ 𝓖
        · rw [dif_pos hc₁] at h₁
          by_cases hc₂ : e₂ ∈ 𝓖
          · rw [dif_pos hc₂] at h₂
            have hφne : φ.labels ⟨e₁, hc₁⟩ ≠ φ.labels ⟨e₂, hc₂⟩ :=
              φ.isColoring ⟨e₁, hc₁⟩ ⟨e₂, hc₂⟩
                (fun heq => hne (congrArg Subtype.val heq)) (by simpa using hnon)
            intro hc
            exact hφne ((Option.some.inj h₁).trans (hc.trans (Option.some.inj h₂).symm))
          · rw [dif_neg hc₂] at h₂
            obtain ⟨v, hv₁, hv₂⟩ := hnon
            have he₁m := mem_uncoloured.mp (hsub₀ e₁ hc₁)
            have he₂ : e₂ ∈ 𝓗 := by
              by_contra hmem
              rw [hinv.out e₂ hmem] at h₂
              exact absurd h₂ (by simp)
            have hexcl := hinv.excl e₁ he₁m.1 he₁m.2 γ₂ ⟨v, hv₁, e₂, he₂, h₂, hv₂⟩
            have hmem₁ : φ.labels ⟨e₁, hc₁⟩ ∈ Lp e₁ := by simpa [Li] using hφmem ⟨e₁, hc₁⟩
            have hγ₁ : γ₁ = φ.labels ⟨e₁, hc₁⟩ := (Option.some.inj h₁).symm
            rw [hγ₁]
            intro hc
            exact hexcl (hc ▸ hmem₁)
        · rw [dif_neg hc₁] at h₁
          by_cases hc₂ : e₂ ∈ 𝓖
          · rw [dif_pos hc₂] at h₂
            obtain ⟨v, hv₁, hv₂⟩ := hnon
            have he₂m := mem_uncoloured.mp (hsub₀ e₂ hc₂)
            have he₁ : e₁ ∈ 𝓗 := by
              by_contra hmem
              rw [hinv.out e₁ hmem] at h₁
              exact absurd h₁ (by simp)
            have hexcl := hinv.excl e₂ he₂m.1 he₂m.2 γ₁ ⟨v, hv₂, e₁, he₁, h₁, hv₁⟩
            have hmem₂ : φ.labels ⟨e₂, hc₂⟩ ∈ Lp e₂ := by simpa [Li] using hφmem ⟨e₂, hc₂⟩
            have hγ₂ : γ₂ = φ.labels ⟨e₂, hc₂⟩ := (Option.some.inj h₂).symm
            rw [hγ₂]
            intro hc
            exact hexcl (hc.symm ▸ hmem₂)
          · rw [dif_neg hc₂] at h₂
            exact hinv.proper e₁ e₂ γ₁ γ₂ h₁ h₂ hne hnon
      · have hleft : uncoloured 𝓗 f' = uncoloured 𝓗 f \ 𝓖 := by
          ext e
          rw [Set.mem_sdiff]
          constructor
          · intro hx
            have h1 : e ∈ 𝓗 := (mem_uncoloured.mp hx).1
            have h2 : f' e = none := (mem_uncoloured.mp hx).2
            have hc : e ∉ 𝓖 := by
              intro hc
              simp only [f'] at h2
              rw [dif_pos hc] at h2
              exact absurd h2 (by simp)
            have hf : f e = none := by
              simp only [f'] at h2
              rw [dif_neg hc] at h2
              exact h2
            exact ⟨mem_uncoloured.mpr ⟨h1, hf⟩, hc⟩
          · intro hx
            obtain ⟨h1, hf⟩ := mem_uncoloured.mp hx.1
            refine mem_uncoloured.mpr ⟨h1, ?_⟩
            simp only [f']
            rw [dif_neg hx.2, hf]
        rw [hleft]
        refine maxDegree_le_of_forall _ (mul_nonneg (pow_nonneg hθnn _) hDnn) (fun v => ?_)
        calc ((hypergraphDegree (uncoloured 𝓗 f \ 𝓖) v : ℕ) : ℝ)
            ≤ (1 - θ) * ((hypergraphMaxDegree (uncoloured 𝓗 f) : ℕ) : ℝ) := hφprog v
          _ ≤ (1 - θ) * ((1 - θ)^i * D) := mul_le_mul_of_nonneg_left hinv.deg (by linarith)
          _ = (1 - θ)^(i+1) * D := by rw [pow_succ]; ring
      · intro e he hf'
        have hc : e ∉ 𝓖 := by
          intro hc
          simp only [f'] at hf'
          rw [dif_pos hc] at hf'
          exact absurd hf' (by simp)
        have hfe : f e = none := by
          simp only [f'] at hf'
          rw [dif_neg hc] at hf'
          exact hf'
        have hmem : e ∈ uncoloured 𝓗 f := mem_uncoloured.mpr ⟨he, hfe⟩
        have hLq : Lq e = Lp e \ lostColours 𝓖 hsub₀ φ Li ⟨e, hmem⟩ := by
          simp only [Lq]
          rw [dif_pos hmem]
        have hloss : ((lostColours 𝓖 hsub₀ φ Li ⟨e, hmem⟩).card : ℝ)
            ≤ ψ * ((1 + β) * ((1 - θ)^i * D)) :=
          hφloss ⟨e, hmem⟩ (by simpa using hc)
        have hsub_lost : lostColours 𝓖 hsub₀ φ Li ⟨e, hmem⟩ ⊆ Lp e :=
          fun γ hγ => lostColours_subset 𝓖 hsub₀ φ Li ⟨e, hmem⟩ (by simpa [Li] using hγ)
        have hcard : ((Lq e).card : ℝ)
            = ((Lp e).card : ℝ) - ((lostColours 𝓖 hsub₀ φ Li ⟨e, hmem⟩).card : ℝ) := by
          rw [hLq, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub_lost,
            Nat.cast_sub (Finset.card_le_card hsub_lost)]
        have hlist := hinv.list_card e he hfe
        have hkey : (1 + β) * D * (1 - (ψ / θ) * (1 - (1 - θ)^i * (1 - θ)))
            = (1 + β) * D * (1 - (ψ / θ) * (1 - (1 - θ)^i))
              - ψ * ((1 + β) * ((1 - θ)^i * D)) := by
          field_simp
          try ring
        rw [pow_succ, hkey]
        linarith
      · intro e he hf' γ hex
        have hc : e ∉ 𝓖 := by
          intro hc
          simp only [f'] at hf'
          rw [dif_pos hc] at hf'
          exact absurd hf' (by simp)
        have hfe : f e = none := by
          simp only [f'] at hf'
          rw [dif_neg hc] at hf'
          exact hf'
        have hmem : e ∈ uncoloured 𝓗 f := mem_uncoloured.mpr ⟨he, hfe⟩
        have hLq : Lq e = Lp e \ lostColours 𝓖 hsub₀ φ Li ⟨e, hmem⟩ := by
          simp only [Lq]
          rw [dif_pos hmem]
        obtain ⟨v, hv, e', he', hf'e', hv'⟩ := hex
        rw [hLq, Finset.mem_sdiff]
        rintro ⟨hγLp, hγlost⟩
        by_cases hc' : e' ∈ 𝓖
        · have hf'' : f' e' = some (φ.labels ⟨e', hc'⟩) := by
            simp only [f']
            rw [dif_pos hc']
          have hγ : φ.labels ⟨e', hc'⟩ = γ := Option.some.inj (hf''.symm.trans hf'e')
          apply hγlost
          simp only [lostColours]
          refine Finset.mem_filter.mpr ⟨by simpa [Li] using hγLp, ?_⟩
          exact ⟨v, by simpa using hv, ⟨e', hc'⟩, by simpa using hv', hγ⟩
        · have hfe' : f e' = some γ := by
            simp only [f'] at hf'e'
            rw [dif_neg hc'] at hf'e'
            exact hf'e'
          have he'mem : e' ∈ 𝓗 := by
            by_contra hmem'
            rw [hinv.out e' hmem'] at hfe'
            exact absurd hfe' (by simp)
          exact absurd hγLp (hinv.excl e he hfe γ ⟨v, hv, e', he'mem, hfe', hv'⟩)
  obtain ⟨f, Lp, hinv⟩ := hmain kstar le_rfl
  haveI : Fintype (uncoloured 𝓗 f) := (Set.toFinite (uncoloured 𝓗 f)).fintype
  have hgreedy : ∀ e : uncoloured 𝓗 f,
      (∑ v ∈ verts (e : Set (Fin n)), (hypergraphDegree (uncoloured 𝓗 f) v - 1))
        < (Lp (e : Set (Fin n))).card := by
    intro e
    have he1 : (e : Set (Fin n)) ∈ 𝓗 := (mem_uncoloured.mp e.2).1
    have he2 : f (e : Set (Fin n)) = none := (mem_uncoloured.mp e.2).2
    have hdeg_le : ∀ v, ((hypergraphDegree (uncoloured 𝓗 f) v : ℕ) : ℝ) ≤ (1 - θ)^kstar * D := by
      intro v
      calc ((hypergraphDegree (uncoloured 𝓗 f) v : ℕ) : ℝ)
          ≤ ((hypergraphMaxDegree (uncoloured 𝓗 f) : ℕ) : ℝ) := by
            exact_mod_cast hypergraphDegree_le_maxDegree (uncoloured 𝓗 f) v
        _ ≤ (1 - θ)^kstar * D := hinv.deg
    have hsum : ((∑ v ∈ verts (e : Set (Fin n)),
          (hypergraphDegree (uncoloured 𝓗 f) v - 1) : ℕ) : ℝ)
        ≤ (r : ℝ) * ((1 - θ)^kstar * D) := by
      rw [Nat.cast_sum]
      calc (∑ v ∈ verts (e : Set (Fin n)),
              ((hypergraphDegree (uncoloured 𝓗 f) v - 1 : ℕ) : ℝ))
          ≤ ∑ v ∈ verts (e : Set (Fin n)), ((hypergraphDegree (uncoloured 𝓗 f) v : ℕ) : ℝ) :=
            Finset.sum_le_sum (fun v _ => by exact_mod_cast Nat.sub_le _ _)
        _ ≤ ∑ v ∈ verts (e : Set (Fin n)), ((1 - θ)^kstar * D) :=
            Finset.sum_le_sum (fun v _ => hdeg_le v)
        _ = ((edgeSize (e : Set (Fin n)) : ℕ) : ℝ) * ((1 - θ)^kstar * D) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            simp [edgeSize]
        _ ≤ (r : ℝ) * ((1 - θ)^kstar * D) :=
            mul_le_mul_of_nonneg_right (hsize ⟨(e : Set (Fin n)), he1⟩)
              (mul_nonneg (pow_nonneg hθnn _) hDnn)
    have hcomp : (r : ℝ) * ((1 - θ)^kstar * D)
        < (1 + β) * D * (1 - (ψ / θ) * (1 - (1 - θ)^kstar)) := by
      have h1 := mul_le_mul_of_nonneg_right hkstar hDnn
      have h2 : (1 + β) * (1 - ψ / θ) / 2 * D < (1 + β) * (1 - ψ / θ) * D := by
        nlinarith [hApos, hDpos]
      have h3 : (1 + β) * (1 - ψ / θ) * D
          ≤ (1 + β) * D * (1 - (ψ / θ) * (1 - (1 - θ)^kstar)) := by
        have hpos : 0 ≤ (1 + β) * D * ((ψ / θ) * (1 - θ)^kstar) := by positivity
        nlinarith [hpos, hApos, hDpos]
      have h4 : (r : ℝ) * ((1 - θ)^kstar * D)
          ≤ (1 + β) * (1 - ψ / θ) / 2 * D := by linarith
      linarith
    have hlist := hinv.list_card (e : Set (Fin n)) he1 he2
    have hfin : ((∑ v ∈ verts (e : Set (Fin n)),
          (hypergraphDegree (uncoloured 𝓗 f) v - 1) : ℕ) : ℝ)
        < ((Lp (e : Set (Fin n))).card : ℝ) := by linarith
    exact_mod_cast hfin
  obtain ⟨χ, hχ⟩ := listColorable_of_card_gt_sum_degree (uncoloured 𝓗 f)
    (fun e : uncoloured 𝓗 f => Lp (e : Set (Fin n))) hgreedy
  obtain ⟨Φ, hΦ⟩ := exists_coloring_of_partial 𝓗 Ltot Lp f hinv.out hinv.list_sub hinv.mem
    hinv.proper hinv.excl χ hχ
  refine ⟨Φ, fun e => ?_⟩
  have h1 : Φ.labels e ∈ Ltot (e : Set (Fin n)) := hΦ e
  rw [hLtot (e : Set (Fin n)) e.2] at h1
  rwa [show (⟨(e : Set (Fin n)), e.2⟩ : 𝓗) = e from Subtype.ext rfl] at h1


end Work.Deep.Kahn
