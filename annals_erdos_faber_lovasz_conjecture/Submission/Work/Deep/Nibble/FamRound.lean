import Submission.Work.Deep.Nibble.r2_own_asm
import Submission.Work.Deep.Nibble.FamW

/-!
# One round of the wasteful Roedl nibble, with the per-set clauses

`nibble_round2_fam_asm` is `Work.Deep.Nibble.nibble_round2_asm` (whose LLL block is
copied verbatim below) with the *family* bad events

    BFamY S = {ω | E[uncovFam 𝓖 · S] + δ|S|/2 ≤ uncovFam 𝓖 ω S}
    BFamW S = {ω | (1+δ)·2rθ²·|S| < badSum 𝓖 ω S}        (S ∈ 𝓕)

(the exponent `θ³δ²|S|/(2048r²)` of the waste tail is the one produced by
`Work.Deep.Nibble.r2_Wfam_tail` in `WfamTail.lean`)

adjoined to the union bound.  The conclusion is `RoundGood` *and* `RoundGoodFamW`.
See `NOTES_SESSION7.md` sections 2 and 4.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

/-- **One round of the wasteful Roedl nibble, with the per-set clauses** (see the
module docstring). -/
theorem nibble_round2_fam_asm {r : ℕ} (hr : 2 ≤ r) {θ δ ε' ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) (hδ0 : 0 < δ) (hδ1 : δ ≤ θ / 100)
    (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1 / 2) (hε'2 : 100 * (ε + ε * (r : ℝ) * θ) ≤ ε')
    (hε0 : 0 < ε) (hε1 : ε ≤ θ / 100) (hεδ : 4 * ε ≤ δ) :
    ∃ Dmin : ℕ, 1 ≤ Dmin ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) (D : ℕ)
        (𝓕 : Finset (Finset V)),
        Dmin ≤ D → D ≤ Fintype.card V → HLin 𝓖 → HUnif 𝓖 r →
        (∀ v : V, |((hd 𝓖 v : ℝ)) - (D : ℝ)| ≤ ε * (D : ℝ)) →
        (∀ (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1) (v : V),
            |(edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((Wv 𝓖 ω v : ℕ) : ℝ))
              - Dlev r θ D| ≤ ε' * Dlev r θ D / 2) →
        (∀ (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1),
            |(edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((uncovF 𝓖 ω).card : ℝ))
              - Real.exp (-θ) * (Fintype.card V : ℝ)| ≤ δ * (Fintype.card V : ℝ) / 2) →
        (∀ (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1),
            (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ))
              ≤ (1 + δ / 2) * (θ - θ * Real.exp (-θ)) * (Fintype.card V : ℝ)) →
        (∀ (S : Finset V) (hS : S ∈ 𝓕) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1),
            |(edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
                (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))
              - Real.exp (-θ) * (S.card : ℝ)| ≤ δ * (S.card : ℝ) / 2) →
        (∀ (S : Finset V) (hS : S ∈ 𝓕) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1),
            (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).prob
                {ω : 𝓖 → Bool | δ / 2 * (S.card : ℝ)
                  ≤ ((uncovFam 𝓖 ω S : ℕ) : ℝ)
                    - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
                        (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))}
              ≤ 4 * Real.exp (- δ ^ 2 * (S.card : ℝ) / (64 * (r : ℝ) ^ 2))) →
        (∀ (S : Finset V) (hS : S ∈ 𝓕) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1),
            (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).prob
                {ω : 𝓖 → Bool | (1 + δ) * (2 * (r : ℝ) * θ ^ 2) * (S.card : ℝ)
                  < ((badSum 𝓖 ω S : ℕ) : ℝ)}
              ≤ 16 * Real.exp (-(θ ^ 3 * δ ^ 2 * (S.card : ℝ)) / (2048 * (r : ℝ) ^ 2))) →
        (hLLLbudget : ∀ (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1),
            (Fintype.card V : ℝ) * (4 * qV r ε' θ D) ≤ 1 / 4) →
        (∀ (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1),
            (∑ S ∈ 𝓕, (4 * Real.exp (- δ ^ 2 * (S.card : ℝ) / (64 * (r : ℝ) ^ 2))
              + 16 * Real.exp (-(θ ^ 3 * δ ^ 2 * (S.card : ℝ)) / (2048 * (r : ℝ) ^ 2)))) ≤ 1 / 16) →
        ∃ ω : 𝓖 → Bool,
          RoundGood 𝓖 r D θ δ ε' (Dlev r θ D) ω ∧ RoundGoodFamW 𝓖 r θ δ 𝓕 ω := by
  classical
  have hr1 : 1 ≤ r := by omega
  obtain ⟨N1, hN1⟩ := r2_num_basic hr hθ0 hθ1 hδ0 hδ1 hε'0 hε'1 hε'2 hε0 hε1 hεδ
  obtain ⟨N2, hN2⟩ := r2_num_sparse hr hθ0 hθ1 hδ0 hδ1 hε'0 hε'1 hε'2 hε0 hε1 hεδ
  obtain ⟨N3, hN3⟩ := r2_num_dense hr hθ0 hθ1 hδ0 hδ1 hε'0 hε'1 hε'2 hε0 hε1 hεδ
  obtain ⟨N4, hN4⟩ := num_strict (r := r) hδ0
  refine ⟨N1 + N2 + N3 + N4 + 1, by omega, ?_⟩
  intro V _ _ 𝓖 D 𝓕 hDmin hDV hl hu hdeg hWvmean hYmean hSmean hYfammean hYfamtail hWfamtail hLLLbudget hroom
  have hD1 : 1 ≤ D := by omega
  have hN1le : N1 ≤ D := by omega
  have hN2le : N2 ≤ D := by omega
  have hN3le : N3 ≤ D := by omega
  have hN4le : N4 ≤ D := by omega
  obtain ⟨_, hthD, hD1ε, hθ2δ, hWvthr0, hq1, hq2, hq3, hq4, hq5, h48r, h1536r, h1e4, hlog48⟩ :=
    hN1 D hN1le
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD1
  have hnpos : (0:ℝ) ≤ (Fintype.card V : ℝ) := by positivity
  have hrpos : (0:ℝ) < (r:ℝ) := by positivity
  have hε1' : ε ≤ 1 := by linarith
  have hθle1 : θ ≤ 1 := by linarith
  have hp0 : 0 ≤ θ/(D:ℝ) := by positivity
  have hp1' : θ/(D:ℝ) < 1 := by linarith
  have hp1 : θ/(D:ℝ) ≤ 1 := hp1'.le
  have hqnn : 0 ≤ qV r ε' θ D := by rw [qV]; positivity
  have h4q0 : 0 ≤ 4 * qV r ε' θ D := by positivity
  have h4q1 : 4 * qV r ε' θ D < 1 := by linarith
  -- degree bounds
  have hdeg_lo : ∀ v : V, (1-ε)*(D:ℝ) ≤ (hd 𝓖 v : ℝ) := by
    intro v; have h := hdeg v; rw [abs_le] at h; linarith [h.1]
  have hdeg_up : ∀ v : V, (hd 𝓖 v : ℝ) ≤ (1+ε)*(D:ℝ) := by
    intro v; have h := hdeg v; rw [abs_le] at h; linarith [h.2]
  have hdeg_2D : ∀ v : V, (hd 𝓖 v : ℝ) ≤ 2*(D:ℝ) := by
    intro v; have h := hdeg_up v; nlinarith [hε1', hDpos]
  have hdeg_one : ∀ v : V, 1 ≤ hd 𝓖 v := by
    intro v
    have h := hdeg_lo v
    have : (1:ℝ) ≤ ((hd 𝓖 v : ℕ) : ℝ) := by linarith [h, hD1ε]
    exact_mod_cast this
  -- cardinality sandwich
  have hsand := (r2_comb_count 𝓖 hr1 hl hu).2.2.2.2 ε (D:ℝ) hε0.le hdeg_lo hdeg_up
  have hGlow : (D:ℝ)*(Fintype.card V :ℝ)/(2*(r:ℝ)) ≤ (Nat.card 𝓖 : ℝ) := by
    have h := hsand.1
    have h3 : (1:ℝ)/2 * (D:ℝ) ≤ (1-ε)*(D:ℝ) := by nlinarith [hε0, hDpos]
    have h4 := mul_le_mul_of_nonneg_right h3 hnpos
    have h2 : (1:ℝ)/2 * ((D:ℝ)*(Fintype.card V :ℝ)) ≤ ((1-ε)*(D:ℝ))*(Fintype.card V :ℝ) := by
      linarith [h4]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*(r:ℝ))]
    linarith [h, h2]
  have hGup : (Nat.card 𝓖 : ℝ) ≤ 2*(D:ℝ)*(Fintype.card V :ℝ)/(r:ℝ) := by
    have h := hsand.2
    rw [le_div_iff₀ hrpos]
    have h3 : (1+ε)*(D:ℝ) ≤ 2*(D:ℝ) := by nlinarith [hε1', hDpos]
    have h4 := mul_le_mul_of_nonneg_right h3 hnpos
    have h2 : ((1+ε)*(D:ℝ))*(Fintype.card V:ℝ) ≤ 2*((D:ℝ)*(Fintype.card V:ℝ)) := by
      linarith [h4]
    linarith [h, h2]
  have hVcard : 0 < Fintype.card V := by omega
  haveI hVne : Nonempty V := Fintype.card_pos_iff.mp hVcard
  have hnne : (Fintype.card V : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hVcard : (0:ℝ) < (Fintype.card V : ℝ))
  have hGne : 𝓖.Nonempty := by
    obtain ⟨v⟩ := hVne
    have h1 : 0 < (thruF 𝓖 v).card := by
      have h := hdeg_one v
      rw [hd_eq_card_thruF] at h
      omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp h1
    exact ⟨e, e.2⟩
  have hNpos : 0 < (Nat.card 𝓖 : ℝ) := by
    obtain ⟨e, he⟩ := hGne
    haveI : Nonempty 𝓖 := ⟨⟨e, he⟩⟩
    exact_mod_cast Nat.card_pos
  have hNne : (Nat.card 𝓖 : ℝ) ≠ 0 := ne_of_gt hNpos
  -- the events
  let A : V → Set (𝓖 → Bool) := fun v => {ω : 𝓖 → Bool |
      v ∉ covX 𝓖 ω ∧ ε' * Dlev r θ D < |((hd (residH 𝓖 ω) v : ℝ)) - Dlev r θ D|}
  let dep : V → Finset V := fun v =>
    Finset.univ.filter (fun w : V => ((Nset 𝓖 v) ∩ (Nset 𝓖 w)).Nonempty)
  let BX : Set (𝓖 → Bool) := {ω | δ * ((Nat.card 𝓖 : ℝ) * (θ/(D:ℝ)))
      < |((keptF 𝓖 ω).card : ℝ) - (Nat.card 𝓖 : ℝ) * (θ/(D:ℝ))|}
  let BY : Set (𝓖 → Bool) := {ω | δ * (Fintype.card V : ℝ)/2
      < |((uncovF 𝓖 ω).card : ℝ)
          - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp (fun ω => ((uncovF 𝓖 ω).card : ℝ))|}
  let BS : Set (𝓖 → Bool) := {ω |
      (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ))
        + (δ/2) * (θ - θ*Real.exp (-θ)) * (Fintype.card V : ℝ) < ((collMult 𝓖 ω : ℕ) : ℝ)}
  let BFam : Set (𝓖 → Bool) :=
    (⋃ S ∈ 𝓕, {ω : 𝓖 → Bool | δ / 2 * (S.card : ℝ)
        ≤ ((uncovFam 𝓖 ω S : ℕ) : ℝ)
          - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))})
    ∪ (⋃ S ∈ 𝓕, {ω : 𝓖 → Bool | (1 + δ) * (2 * (r:ℝ) * θ ^ 2) * (S.card : ℝ)
        < ((badSum 𝓖 ω S : ℕ) : ℝ)})
  -- the per-vertex probability bound
  have hAprob : ∀ v : V, (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (A v) ≤ qV r ε' θ D := by
    intro v
    have hD'pos : 0 < Dlev r θ D := Dlev_pos hθ0 hD1 hthD
    have hthr : 50 * (r:ℝ) * Real.sqrt (2*(D:ℝ)) < ε' * Dlev r θ D / 2 := by
      have hDlev := Dlev_lower hr1 hθ0 hD1 hthD
      have hDsqrt : 0 < Real.sqrt (D:ℝ) := Real.sqrt_pos.mpr hDpos
      have hstep1 : 100*(r:ℝ)*Real.sqrt 2*Real.sqrt (D:ℝ)*Real.exp (2*θ*((r:ℝ)-1))
          < ε'*(D:ℝ) := by
        have h := mul_lt_mul_of_pos_right hWvthr0 hDsqrt
        have h2 : (ε' * Real.sqrt (D:ℝ)) * Real.sqrt (D:ℝ) = ε'*(D:ℝ) := by
          rw [mul_assoc, Real.mul_self_sqrt hDpos.le]
        rw [h2] at h
        linarith [h]
      have hstep2 : 100*(r:ℝ)*Real.sqrt 2*Real.sqrt (D:ℝ)
          < ε'*((D:ℝ)*Real.exp (-(2*θ*((r:ℝ)-1)))) := by
        have hEF : Real.exp (2*θ*((r:ℝ)-1)) * Real.exp (-(2*θ*((r:ℝ)-1))) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        have hE2 : 0 < Real.exp (-(2*θ*((r:ℝ)-1))) := Real.exp_pos _
        have h1 := mul_lt_mul_of_pos_right hstep1 hE2
        have h2 : (100*(r:ℝ)*Real.sqrt 2*Real.sqrt (D:ℝ)*Real.exp (2*θ*((r:ℝ)-1)))
              * Real.exp (-(2*θ*((r:ℝ)-1))) = 100*(r:ℝ)*Real.sqrt 2*Real.sqrt (D:ℝ) := by
          rw [mul_assoc, hEF, mul_one]
        have h3 : ε'*(D:ℝ)*Real.exp (-(2*θ*((r:ℝ)-1)))
            = ε'*((D:ℝ)*Real.exp (-(2*θ*((r:ℝ)-1)))) := by ring
        linarith [h1, h2, h3]
      have hroot2 : Real.sqrt (2*(D:ℝ)) = Real.sqrt 2 * Real.sqrt (D:ℝ) :=
        Real.sqrt_mul (by norm_num) (D:ℝ)
      have hDlev2 : ε'*((D:ℝ)*Real.exp (-(2*θ*((r:ℝ)-1))))/2 ≤ ε'*Dlev r θ D/2 := by
        have h := mul_le_mul_of_nonneg_left hDlev (by positivity : 0 ≤ ε'/2)
        linarith [h]
      rw [hroot2]
      linarith [hstep2, hDlev2]
    have htail := r2_Wv_tail 𝓖 hr hθ0 hD1 hp0 hp1' hl hu hdeg_2D hε'0 hD'pos hthr v
    have hsub : A v ⊆ {ω : 𝓖 → Bool | ε' * Dlev r θ D / 2 ≤
        |((Wv 𝓖 ω v : ℕ) : ℝ)
          - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp (fun ω => ((Wv 𝓖 ω v : ℕ) : ℝ))|} := by
      intro ω hω
      simp only [A, Set.mem_setOf_eq] at hω
      obtain ⟨hunc, hbad⟩ := hω
      simp only [Set.mem_setOf_eq]
      have hW := Wv_eq_hd_residH 𝓖 ω v hunc
      rw [hW] at hbad
      have hmean := hWvmean hp0 hp1 v
      have htri := abs_sub_le ((Wv 𝓖 ω v : ℕ) : ℝ)
        ((edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp (fun ω => ((Wv 𝓖 ω v : ℕ) : ℝ)))
        (Dlev r θ D)
      linarith [hbad, hmean, htri]
    calc (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (A v)
        ≤ (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob {ω : 𝓖 → Bool | ε' * Dlev r θ D / 2 ≤
            |((Wv 𝓖 ω v : ℕ) : ℝ)
              - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp (fun ω => ((Wv 𝓖 ω v : ℕ) : ℝ))|} :=
          FinProb.prob_mono _ hsub
      _ ≤ 4 * Real.exp (-(ε' * Dlev r θ D / 2) ^ 2 / (16 * (r:ℝ)^2 * (2*(D:ℝ)))) := htail
      _ = qV r ε' θ D := by
          rw [qV]
          have hone : -(ε' * Dlev r θ D / 2) ^ 2 / (16 * (r:ℝ) ^ 2 * (2 * (D:ℝ)))
              = -(ε' * Dlev r θ D) ^ 2 / (128 * (r:ℝ) ^ 2 * (D:ℝ)) := by ring
          rw [hone]
  -- the independence condition
  have hfar : ∀ i : V, ∀ S : Finset V, (∀ j ∈ S, j ∉ dep i ∧ j ≠ i) →
      (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).Indep (A i) (⋂ j ∈ S, (A j)ᶜ) := by
    intro i S hS
    have hdep : ∀ j ∈ S, ¬ ((Nset 𝓖 i) ∩ (Nset 𝓖 j)).Nonempty := by
      intro j hjS
      have hh := (hS j hjS).1
      simp only [dep, Finset.mem_filter, Finset.mem_univ, true_and] at hh
      exact hh
    have hdisj : Disjoint (Nset 𝓖 i) (S.biUnion (fun j => Nset 𝓖 j)) := by
      rw [Finset.disjoint_left]
      intro f hfi hfj
      obtain ⟨j, hjS, hfj'⟩ := Finset.mem_biUnion.mp hfj
      exact hdep j hjS ⟨f, Finset.mem_inter.mpr ⟨hfi, hfj'⟩⟩
    have hDA : DependsOn (Nset 𝓖 i) (A i) := dependsOn_event 𝓖 i ε' (Dlev r θ D)
    have hDB : DependsOn (S.biUnion (fun j => Nset 𝓖 j)) (⋂ j ∈ S, (A j)ᶜ) := by
      apply DependsOn.biInter
      intro j hjS
      exact (dependsOn_event 𝓖 j ε' (Dlev r θ D)).compl.mono
        (Finset.subset_biUnion_of_mem (fun j => Nset 𝓖 j) hjS)
    have hind := Prob.pi_prob_inter_eq_mul_of_disjoint
      (μ := fun _ : 𝓖 => boolProb (θ/(D:ℝ)) hp0 hp1) hdisj hDA hDB
    show (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (A i ∩ ⋂ j ∈ S, (A j)ᶜ)
      = (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (A i)
        * (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (⋂ j ∈ S, (A j)ᶜ)
    exact hind
  -- the LLL bound
  have hbound : ∀ i : V, (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (A i)
      ≤ (4 * qV r ε' θ D) * ∏ j ∈ dep i, (1 - 4 * qV r ε' θ D) := by
    intro i
    have hdep := dep_card_le 𝓖 hr1 hl hu hε0.le hε1'
      (by exact_mod_cast hD1 : (1:ℝ) ≤ (D:ℝ)) hdeg_up i
    have hcard : ((dep i).card : ℝ) * (4 * qV r ε' θ D) ≤ 1/4 := by
      have h1 : ((dep i).card : ℝ) * (4 * qV r ε' θ D)
          ≤ (100 * (r:ℝ)^3 * (D:ℝ)^3) * (4 * qV r ε' θ D) :=
        mul_le_mul_of_nonneg_right hdep h4q0
      have h2 : (100 * (r:ℝ)^3 * (D:ℝ)^3) * (4 * qV r ε' θ D) ≤ 1/4 := by
        nlinarith [hq2, h4q0]
      linarith
    have hprod : 3/4 ≤ ∏ j ∈ dep i, (1 - 4 * qV r ε' θ D) := by
      rw [Finset.prod_const]
      have hb := one_sub_mul_le_pow h4q0 (le_of_lt h4q1) ((dep i).card)
      nlinarith [hb, hcard]
    calc (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (A i) ≤ qV r ε' θ D := hAprob i
      _ ≤ (4 * qV r ε' θ D) * ∏ j ∈ dep i, (1 - 4 * qV r ε' θ D) := by
          nlinarith [hprod, h4q0]
  have hLLL : (∏ i : V, (1 - 4 * qV r ε' θ D))
      ≤ (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (⋂ i, (A i)ᶜ) :=
    Prob.lll_general (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1) A dep (fun _ : V => 4 * qV r ε' θ D)
      (fun _ => h4q0) (fun _ => h4q1) hfar hbound
  have hGprob : Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ)))
      ≤ (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (⋂ i, (A i)ᶜ) := by
    have hprod : (∏ i : V, (1 - 4 * qV r ε' θ D))
        = (1 - 4 * qV r ε' θ D) ^ (Fintype.card V) := by
      rw [Finset.prod_const, Finset.card_univ]
    have hLLL' : (1 - 4 * qV r ε' θ D) ^ (Fintype.card V)
        ≤ (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (⋂ i, (A i)ᶜ) := by
      rw [← hprod]; exact hLLL
    have h1 : Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ)))
        = Real.exp (-(2 * (4 * qV r ε' θ D) * ((Fintype.card V : ℕ) : ℝ))) := by
      congr 1; ring
    rw [h1]
    exact le_trans (one_sub_pow_ge_exp h4q0 (by linarith [hq1]) (Fintype.card V)) hLLL'
  -- probability of the three global bad events
  have hsubX : BX ⊆ {ω : 𝓖 → Bool | δ * ((Nat.card 𝓖 : ℝ) * (θ/(D:ℝ))) ≤
      |((keptF 𝓖 ω).card : ℝ)
        - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp (fun ω => ((keptF 𝓖 ω).card : ℝ))|} := by
    intro ω hω
    simp only [BX, Set.mem_setOf_eq] at hω ⊢
    rw [(r2_exp_basic 𝓖 hp0 hp1).1]
    exact le_of_lt hω
  have hsubY : BY ⊆ {ω : 𝓖 → Bool | δ * (Fintype.card V : ℝ)/2 ≤
      |((uncovF 𝓖 ω).card : ℝ)
        - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp (fun ω => ((uncovF 𝓖 ω).card : ℝ))|} := by
    intro ω hω
    simp only [BY, Set.mem_setOf_eq] at hω ⊢
    exact le_of_lt hω
  have hsubS : BS ⊆ {ω : 𝓖 → Bool | (δ/2) * (θ - θ*Real.exp (-θ)) * (Fintype.card V : ℝ) ≤
      |((collMult 𝓖 ω : ℕ) : ℝ)
        - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ))|} := by
    intro ω hω
    simp only [BS, Set.mem_setOf_eq] at hω ⊢
    have hle := le_abs_self (((collMult 𝓖 ω : ℕ) : ℝ)
      - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ)))
    linarith [hω, hle]
  have hsqrtN_le : Real.sqrt (Nat.card 𝓖 : ℝ)
      ≤ Real.sqrt (2*(D:ℝ)*(Fintype.card V :ℝ)/(r:ℝ)) := Real.sqrt_le_sqrt hGup
  have hexc_final : ∀ {a : ℝ}, 8 * qV r ε' θ D * (Fintype.card V : ℝ) + Real.log 48 ≤ a →
      Real.exp (-a) ≤ Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 48 := by
    intro a ha
    have h1 : Real.exp (-a) ≤ Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ) + Real.log 48)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ) + Real.log 48))
        = Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 48 := by
      have harg : -(8 * qV r ε' θ D * (Fintype.card V : ℝ) + Real.log 48)
          = -(8 * qV r ε' θ D * (Fintype.card V : ℝ)) + -(Real.log 48) := by ring
      rw [harg, Real.exp_add]
      have h48 : Real.exp (-(Real.log 48)) = 1/48 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]
        norm_num
      rw [h48]
      ring
    linarith [h1, h2]
  have hPX : (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob BX
      ≤ Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 12 := by
    have htpos : 0 < δ * ((Nat.card 𝓖 : ℝ) * (θ/(D:ℝ))) := by positivity
    by_cases hn : nThresh r θ δ D ≤ (Fintype.card V : ℝ)
    · obtain ⟨hsp1, hsp2, hsp3, hsp4⟩ := hN2 D (Fintype.card V) hN2le hDV hn
      have hlow : δ * θ * (Fintype.card V:ℝ) / (2*(r:ℝ))
          ≤ δ * ((Nat.card 𝓖:ℝ) * (θ/(D:ℝ))) := by
        have hmul := mul_le_mul_of_nonneg_left hGlow (by positivity : 0 ≤ δ*(θ/(D:ℝ)))
        have hL : δ*(θ/(D:ℝ)) * ((D:ℝ)*(Fintype.card V:ℝ)/(2*(r:ℝ)))
            = δ * θ * (Fintype.card V:ℝ) / (2*(r:ℝ)) := by field_simp
        have hR : δ*(θ/(D:ℝ)) * (Nat.card 𝓖:ℝ) = δ * ((Nat.card 𝓖:ℝ)*(θ/(D:ℝ))) := by ring
        rwa [hL, hR] at hmul
      have ht : 50 * Real.sqrt (Nat.card 𝓖:ℝ) < δ * ((Nat.card 𝓖:ℝ) * (θ/(D:ℝ))) := by
        have h1 : 50 * Real.sqrt (Nat.card 𝓖:ℝ)
            ≤ 50 * Real.sqrt (2*(D:ℝ)*(Fintype.card V:ℝ)/(r:ℝ)) := by linarith [hsqrtN_le]
        exact lt_of_le_of_lt h1 (lt_of_lt_of_le hsp1 hlow)
      have htail := r2_X_tail 𝓖 hD1 hp0 hp1 hGne ht
      have hexp : 8 * qV r ε' θ D * (Fintype.card V : ℝ) + Real.log 48
          ≤ (δ * ((Nat.card 𝓖 : ℝ) * (θ/(D:ℝ))))^2 / (16 * (Nat.card 𝓖 : ℝ)) := by
        have hkey : δ^2*θ^2*(Fintype.card V:ℝ)/(32*(r:ℝ)*(D:ℝ))
            ≤ (δ * ((Nat.card 𝓖:ℝ) * (θ/(D:ℝ))))^2/(16*(Nat.card 𝓖:ℝ)) := by
          have hmul := mul_le_mul_of_nonneg_left hGlow (by positivity : 0 ≤ δ^2*θ^2/(16*(D:ℝ)^2))
          have h1 : δ^2*θ^2/(16*(D:ℝ)^2) * ((D:ℝ)*(Fintype.card V:ℝ)/(2*(r:ℝ)))
              = δ^2*θ^2*(Fintype.card V:ℝ)/(32*(r:ℝ)*(D:ℝ)) := by field_simp; ring
          have h2 : δ^2*θ^2/(16*(D:ℝ)^2) * (Nat.card 𝓖:ℝ)
              = (δ * ((Nat.card 𝓖:ℝ)*(θ/(D:ℝ))))^2/(16*(Nat.card 𝓖:ℝ)) := by
            field_simp
          rwa [h1, h2] at hmul
        have h5 : δ^2*θ^2*(Fintype.card V:ℝ)/(128*(r:ℝ)*(D:ℝ))
            ≤ δ^2*θ^2*(Fintype.card V:ℝ)/(32*(r:ℝ)*(D:ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [hrpos, hDpos])
        linarith [hsp3, h5, hkey]
      calc (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob BX
          ≤ 4 * Real.exp (-(δ * ((Nat.card 𝓖:ℝ) * (θ/(D:ℝ))))^2/(16*(Nat.card 𝓖:ℝ))) :=
            le_trans (FinProb.prob_mono _ hsubX) htail
        _ ≤ Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 12 := by
            have he : Real.exp ((-((δ * ((Nat.card 𝓖:ℝ) * (θ/(D:ℝ))))^2))/(16*(Nat.card 𝓖:ℝ)))
                = Real.exp (-((δ * ((Nat.card 𝓖:ℝ) * (θ/(D:ℝ))))^2/(16*(Nat.card 𝓖:ℝ)))) := by
              congr 1
              ring
            rw [he]
            have h1 := hexc_final hexp
            calc 4 * Real.exp (-((δ * ((Nat.card 𝓖:ℝ) * (θ/(D:ℝ))))^2/(16*(Nat.card 𝓖:ℝ))))
                ≤ 4 * (Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 48) :=
                  mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 4)
              _ = Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 12 := by ring
    · obtain ⟨hdn1, hdn2, hdn3⟩ := hN3 D (Fintype.card V) hN3le hDV hn
      have hvar := (r2_var 𝓖 hr hθ0 (by linarith : θ ≤ 1/2) hD1 hp0 hp1 hl hu hdeg_2D).1
      have hcheb := prob_abs_sub_exp_le_variance (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1)
        (fun ω => ((keptF 𝓖 ω).card : ℝ)) htpos
      have hstep : (1 - θ/(D:ℝ))/(δ^2*(Nat.card 𝓖:ℝ)*(θ/(D:ℝ)))
          ≤ 2*(r:ℝ)/(δ^2*θ*(Fintype.card V:ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : (1 - θ/(D:ℝ)) ≤ 1 := by linarith [hp0]
        have h2 : θ*(Fintype.card V:ℝ) ≤ 2*(r:ℝ)*((Nat.card 𝓖:ℝ)*(θ/(D:ℝ))) := by
          have hthis := hGlow
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*(r:ℝ))] at hthis
          have hm := mul_le_mul_of_nonneg_right hthis (by positivity : 0 ≤ θ/(D:ℝ))
          have he : (D:ℝ)*(Fintype.card V:ℝ)*(θ/(D:ℝ)) = θ*(Fintype.card V:ℝ) := by field_simp
          have he2 : ((Nat.card 𝓖:ℝ)*(2*(r:ℝ)))*(θ/(D:ℝ))
              = 2*(r:ℝ)*((Nat.card 𝓖:ℝ)*(θ/(D:ℝ))) := by ring
          rwa [he, he2] at hm
        have h3 : (1 - θ/(D:ℝ)) * (δ^2*θ*(Fintype.card V:ℝ)) ≤ δ^2*θ*(Fintype.card V:ℝ) := by
          have hh := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ δ^2*θ*(Fintype.card V:ℝ))
          linarith only [hh]
        have h4 : δ^2*θ*(Fintype.card V:ℝ) ≤ 2*(r:ℝ)*(δ^2*(Nat.card 𝓖:ℝ)*(θ/(D:ℝ))) := by
          have hh := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ δ^2)
          linarith only [hh]
        linarith only [h3, h4]
      calc (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob BX
          ≤ variance (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1) (fun ω => ((keptF 𝓖 ω).card : ℝ))
              / (δ * ((Nat.card 𝓖 : ℝ) * (θ/(D:ℝ))))^2 :=
            le_trans (FinProb.prob_mono _ hsubX) hcheb
        _ = (1 - θ/(D:ℝ))/(δ^2*(Nat.card 𝓖:ℝ)*(θ/(D:ℝ))) := by
            rw [hvar]; field_simp
        _ ≤ 2*(r:ℝ)/(δ^2*θ*(Fintype.card V:ℝ)) := hstep
        _ ≤ Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 12 := hdn2
  have hPY : (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob BY
      ≤ Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 12 := by
    have ht : 50 * (r:ℝ) * Real.sqrt (Fintype.card V : ℝ) < δ * (Fintype.card V : ℝ)/2 := by
      have hstrict : (10:ℝ)^6 * (r:ℝ)^2 < δ^2 * (D:ℝ) := by
        have h := hN4 D hN4le
        norm_num at h ⊢
        exact h
      have hDn : (D:ℝ) ≤ (Fintype.card V :ℝ) := by exact_mod_cast hDV
      have hsqrtn : 0 < Real.sqrt (Fintype.card V : ℝ) := by
        rw [Real.sqrt_pos]; exact_mod_cast hVcard
      have hkey : 100*(r:ℝ) < δ * Real.sqrt (Fintype.card V : ℝ) := by
        have hsq : (100*(r:ℝ))^2 < (δ * Real.sqrt (Fintype.card V:ℝ))^2 := by
          have hL : (100*(r:ℝ))^2 = 10^4 * (r:ℝ)^2 := by ring
          have hR : (δ * Real.sqrt (Fintype.card V:ℝ))^2 = δ^2 * (Fintype.card V:ℝ) := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
          rw [hL, hR]
          nlinarith only [hstrict, hDn, hδ0, hrpos, hnpos]
        have h1 : Real.sqrt ((100*(r:ℝ))^2) < Real.sqrt ((δ * Real.sqrt (Fintype.card V:ℝ))^2) :=
          Real.sqrt_lt_sqrt (by positivity) hsq
        rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h1
      have h2 : (100*(r:ℝ)) * Real.sqrt (Fintype.card V:ℝ) < δ * (Fintype.card V:ℝ) := by
        have h3 := mul_lt_mul_of_pos_right hkey hsqrtn
        have h4 : δ * Real.sqrt (Fintype.card V:ℝ) * Real.sqrt (Fintype.card V:ℝ)
            = δ * (Fintype.card V:ℝ) := by
          rw [mul_assoc, Real.mul_self_sqrt (by positivity)]
        rw [h4] at h3
        linarith only [h3]
      linarith only [h2]
    have htail := r2_Y_tail 𝓖 hr hu hθ0 hD1 hp0 hp1' ht
    have hexp : 8 * qV r ε' θ D * (Fintype.card V : ℝ) + Real.log 48
        ≤ (δ * (Fintype.card V : ℝ)/2)^2/(16*(r:ℝ)^2*(Fintype.card V:ℝ)) := by
      have h1 : 8*qV r ε' θ D * (Fintype.card V:ℝ)
          ≤ δ^2 * (Fintype.card V:ℝ)/(128*(r:ℝ)^2) := by
        have h := mul_le_mul_of_nonneg_right hq3 hnpos
        rwa [show (δ^2/(128*(r:ℝ)^2)) * (Fintype.card V:ℝ)
              = δ^2*(Fintype.card V:ℝ)/(128*(r:ℝ)^2) by ring] at h
      have h2 : Real.log 48 ≤ δ^2 * (Fintype.card V:ℝ)/(128*(r:ℝ)^2) := by
        refine le_trans hlog48 ?_
        have hDn : (D:ℝ) ≤ (Fintype.card V :ℝ) := by exact_mod_cast hDV
        have hh := mul_le_mul_of_nonneg_right hDn (by positivity : 0 ≤ δ^2/(128*(r:ℝ)^2))
        have hL : (D:ℝ) * (δ^2/(128*(r:ℝ)^2)) = δ^2*(D:ℝ)/(128*(r:ℝ)^2) := by ring
        have hR : (Fintype.card V:ℝ) * (δ^2/(128*(r:ℝ)^2))
            = δ^2*(Fintype.card V:ℝ)/(128*(r:ℝ)^2) := by ring
        rwa [hL, hR] at hh
      have h3 : (δ * (Fintype.card V:ℝ)/2)^2/(16*(r:ℝ)^2*(Fintype.card V:ℝ))
          = δ^2*(Fintype.card V:ℝ)/(64*(r:ℝ)^2) := by field_simp; ring
      have h4 : δ^2*(Fintype.card V:ℝ)/(128*(r:ℝ)^2) + δ^2*(Fintype.card V:ℝ)/(128*(r:ℝ)^2)
          = δ^2*(Fintype.card V:ℝ)/(64*(r:ℝ)^2) := by ring
      rw [h3]
      linarith only [h1, h2, h4]
    calc (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob BY
        ≤ 4 * Real.exp (-(δ * (Fintype.card V:ℝ)/2)^2/(16*(r:ℝ)^2*(Fintype.card V:ℝ))) :=
          le_trans (FinProb.prob_mono _ hsubY) htail
      _ ≤ Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 12 := by
          have he : Real.exp ((-((δ * (Fintype.card V:ℝ)/2)^2))/(16*(r:ℝ)^2*(Fintype.card V:ℝ)))
              = Real.exp (-((δ * (Fintype.card V:ℝ)/2)^2/(16*(r:ℝ)^2*(Fintype.card V:ℝ)))) := by
            congr 1
            ring
          rw [he]
          have h1 := hexc_final hexp
          calc 4 * Real.exp (-((δ * (Fintype.card V:ℝ)/2)^2/(16*(r:ℝ)^2*(Fintype.card V:ℝ))))
              ≤ 4 * (Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 48) :=
                mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 4)
            _ = Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 12 := by ring
  have hPS : (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob BS
      ≤ Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 12 := by
    have hg := theta_one_sub_exp_neg hθ0.le hθle1
    have hgpos : 0 < θ - θ*Real.exp (-θ) := by
      have h : Real.exp (-θ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have h2 : θ * Real.exp (-θ) < θ * 1 := mul_lt_mul_of_pos_left h hθ0
      linarith only [h2]
    have hnpos' : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hVcard
    have htpos : 0 < (δ/2) * (θ - θ*Real.exp (-θ)) * (Fintype.card V : ℝ) :=
      mul_pos (mul_pos (by linarith [hδ0]) hgpos) hnpos'
    have hXpos : 0 < ((δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ))^2 := by positivity
    by_cases hn : nThresh r θ δ D ≤ (Fintype.card V : ℝ)
    · obtain ⟨hsp1, hsp2, hsp3, hsp4⟩ := hN2 D (Fintype.card V) hN2le hDV hn
      have ht : 100*(r:ℝ)*Real.sqrt (Nat.card 𝓖:ℝ)
          < (δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ) := by
        have h1 : 100*(r:ℝ)*Real.sqrt (Nat.card 𝓖:ℝ)
            ≤ 100*(r:ℝ)*Real.sqrt (2*(D:ℝ)*(Fintype.card V:ℝ)/(r:ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrtN_le (by positivity)
        exact lt_of_le_of_lt h1 hsp2
      have htail := r2_S_tail 𝓖 hr hu hD1 hp0 hp1 hGne ht
      have hexp : 8 * qV r ε' θ D * (Fintype.card V : ℝ) + Real.log 48
          ≤ ((δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ))^2
              /(16*(2*(r:ℝ))^2*(Nat.card 𝓖:ℝ)) := by
        have hnum : ((δ/2)*(θ^2/2)*(Fintype.card V:ℝ))^2
            ≤ ((δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ))^2 := by
          apply pow_le_pow_left₀ (by positivity : 0 ≤ (δ/2)*(θ^2/2)*(Fintype.card V:ℝ))
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) hnpos
        have hden : 16*(2*(r:ℝ))^2*(Nat.card 𝓖:ℝ)
            ≤ 128*(r:ℝ)*(D:ℝ)*(Fintype.card V:ℝ) := by
          have h := mul_le_mul_of_nonneg_left hGup (by positivity : 0 ≤ 16*(2*(r:ℝ))^2)
          rw [show 16*(2*(r:ℝ))^2 * (2*(D:ℝ)*(Fintype.card V:ℝ)/(r:ℝ))
              = 128*(r:ℝ)*(D:ℝ)*(Fintype.card V:ℝ) by field_simp <;> ring] at h
          exact h
        have hdiv := div_le_div_of_nonneg_left
          (a := ((δ/2)*(θ^2/2)*(Fintype.card V:ℝ))^2)
          (by positivity) (by positivity : 0 < 16*(2*(r:ℝ))^2*(Nat.card 𝓖:ℝ)) hden
        have hC : ((δ/2)*(θ^2/2)*(Fintype.card V:ℝ))^2/(128*(r:ℝ)*(D:ℝ)*(Fintype.card V:ℝ))
            = δ^2*θ^4*(Fintype.card V:ℝ)/(2048*(r:ℝ)*(D:ℝ)) := by field_simp <;> ring
        have hnum2 : ((δ/2)*(θ^2/2)*(Fintype.card V:ℝ))^2/(16*(2*(r:ℝ))^2*(Nat.card 𝓖:ℝ))
            ≤ ((δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ))^2
                /(16*(2*(r:ℝ))^2*(Nat.card 𝓖:ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          exact mul_le_mul_of_nonneg_right hnum (by positivity)
        rw [hC] at hdiv
        exact le_trans hsp4 (le_trans hdiv hnum2)
      calc (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob BS
          ≤ 4 * Real.exp (-((δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ))^2
              /(16*(2*(r:ℝ))^2*(Nat.card 𝓖:ℝ))) :=
            le_trans (FinProb.prob_mono _ hsubS) htail
        _ ≤ Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 12 := by
            have he : Real.exp ((-(((δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ))^2))
                  /(16*(2*(r:ℝ))^2*(Nat.card 𝓖:ℝ)))
                = Real.exp (-(((δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ))^2
                    /(16*(2*(r:ℝ))^2*(Nat.card 𝓖:ℝ)))) := by
              congr 1
              ring
            rw [he]
            have h1 := hexc_final hexp
            calc 4 * Real.exp (-(((δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ))^2
                /(16*(2*(r:ℝ))^2*(Nat.card 𝓖:ℝ))))
                ≤ 4 * (Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 48) :=
                  mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 4)
              _ = Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 12 := by ring
    · obtain ⟨hdn1, hdn2, hdn3⟩ := hN3 D (Fintype.card V) hN3le hDV hn
      have hvar := (r2_var 𝓖 hr hθ0 (by linarith : θ ≤ 1/2) hD1 hp0 hp1 hl hu hdeg_2D).2
      have hcheb := prob_abs_sub_exp_le_variance (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1)
        (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ)) htpos
      have hstep : 4*(r:ℝ)*θ*(Fintype.card V:ℝ)
            / ((δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ))^2
          ≤ 64*(r:ℝ)/(δ^2*θ^3*(Fintype.card V:ℝ)) := by
        have hg2 : (θ^2/2)^2 ≤ (θ - θ*Real.exp (-θ))^2 := pow_le_pow_left₀ (by positivity) hg 2
        have h4 : θ^4 ≤ 4*(θ - θ*Real.exp (-θ))^2 := by
          have h5 : (θ^2/2)^2 = θ^4/4 := by ring
          rw [h5] at hg2
          linarith only [hg2]
        rw [div_le_div_iff₀ hXpos (by positivity)]
        have h5 : 4*θ^4 ≤ 16*(θ - θ*Real.exp (-θ))^2 := by linarith only [h4]
        have h6 : 4*(r:ℝ)*θ*(Fintype.card V:ℝ) * (δ^2*θ^3*(Fintype.card V:ℝ))
            ≤ 64*(r:ℝ) * ((δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ))^2 := by
          have hh := mul_le_mul_of_nonneg_right h5
            (by positivity : 0 ≤ (r:ℝ)*δ^2*(Fintype.card V:ℝ)^2)
          rw [show 4*(r:ℝ)*θ*(Fintype.card V:ℝ) * (δ^2*θ^3*(Fintype.card V:ℝ))
                = 4*θ^4*((r:ℝ)*δ^2*(Fintype.card V:ℝ)^2) by ring,
              show 64*(r:ℝ) * ((δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ))^2
                = 16*(θ - θ*Real.exp (-θ))^2*((r:ℝ)*δ^2*(Fintype.card V:ℝ)^2) by ring]
          exact hh
        exact h6
      calc (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob BS
          ≤ variance (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1) (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ))
              / ((δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ))^2 :=
            le_trans (FinProb.prob_mono _ hsubS) hcheb
        _ ≤ 4*(r:ℝ)*θ*(Fintype.card V:ℝ)
              / ((δ/2)*(θ - θ*Real.exp (-θ))*(Fintype.card V:ℝ))^2 := by
            rw [div_le_div_iff₀ hXpos hXpos]
            nlinarith only [hvar, hXpos]
        _ ≤ 64*(r:ℝ)/(δ^2*θ^3*(Fintype.card V:ℝ)) := hstep
        _ ≤ Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) / 12 := hdn3  -- the family bad event and its probability
  have hPFam : (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob BFam ≤ 1 / 16 := by
    have h1 : (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob
        (⋃ S ∈ 𝓕, {ω : 𝓖 → Bool | δ / 2 * (S.card : ℝ)
          ≤ ((uncovFam 𝓖 ω S : ℕ) : ℝ)
            - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp
                (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))})
        ≤ ∑ S ∈ 𝓕, 4 * Real.exp (- δ ^ 2 * (S.card : ℝ) / (64 * (r:ℝ) ^ 2)) := by
      refine le_trans (FinProb.prob_iUnion_le _ 𝓕 (fun S => {ω : 𝓖 → Bool | δ / 2 * (S.card : ℝ)
          ≤ ((uncovFam 𝓖 ω S : ℕ) : ℝ)
            - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp
                (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))})) ?_
      exact Finset.sum_le_sum fun S hS => hYfamtail S hS hp0 hp1
    have h2 : (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob
        (⋃ S ∈ 𝓕, {ω : 𝓖 → Bool | (1 + δ) * (2 * (r:ℝ) * θ ^ 2) * (S.card : ℝ)
          < ((badSum 𝓖 ω S : ℕ) : ℝ)})
        ≤ ∑ S ∈ 𝓕, 16 * Real.exp (-(θ ^ 3 * δ ^ 2 * (S.card : ℝ)) / (2048 * (r:ℝ) ^ 2)) := by
      refine le_trans (FinProb.prob_iUnion_le _ 𝓕 (fun S => {ω : 𝓖 → Bool |
          (1 + δ) * (2 * (r:ℝ) * θ ^ 2) * (S.card : ℝ)
            < ((badSum 𝓖 ω S : ℕ) : ℝ)})) ?_
      exact Finset.sum_le_sum fun S hS => hWfamtail S hS hp0 hp1
    have hBFam : BFam = (⋃ S ∈ 𝓕, {ω : 𝓖 → Bool | δ / 2 * (S.card : ℝ)
          ≤ ((uncovFam 𝓖 ω S : ℕ) : ℝ)
            - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp
                (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))})
        ∪ (⋃ S ∈ 𝓕, {ω : 𝓖 → Bool | (1 + δ) * (2 * (r:ℝ) * θ ^ 2) * (S.card : ℝ)
          < ((badSum 𝓖 ω S : ℕ) : ℝ)}) := rfl
    rw [hBFam]
    refine le_trans (FinProb.prob_union_le _ _ _) ?_
    have hroom' := hroom hp0 hp1
    rw [Finset.sum_add_distrib] at hroom'
    linarith [h1, h2]
  -- combine
  have hexcpos : 0 < Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) := Real.exp_pos _
  have hexphalf : (1:ℝ) / 2 ≤ Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) := by
    have hLLL' := hLLLbudget hp0 hp1
    have h1 : Real.exp (-(1/2:ℝ)) ≤ Real.exp (-(8 * qV r ε' θ D * (Fintype.card V : ℝ))) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hLLL']
    refine le_trans ?_ h1
    have h2 := Real.add_one_le_exp (-(1/2:ℝ))
    linarith
  have hcombo : 0 < (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob
      ((⋂ i, (A i)ᶜ) \ (BX ∪ BY ∪ BS ∪ BFam)) := by
    have hUB : (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (BX ∪ BY ∪ BS ∪ BFam)
        ≤ Real.exp (-(8*qV r ε' θ D * (Fintype.card V:ℝ)))/12
          + Real.exp (-(8*qV r ε' θ D * (Fintype.card V:ℝ)))/12
          + Real.exp (-(8*qV r ε' θ D * (Fintype.card V:ℝ)))/12 + 1/16 := by
      have h1 := prob_union3_le (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1) BX BY BS
      have h2 := FinProb.prob_union_le (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1) (BX ∪ BY ∪ BS) BFam
      linarith [h1, h2, hPX, hPY, hPS, hPFam]
    have h3 := prob_sdiff_ge (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1) (⋂ i, (A i)ᶜ)
      (BX ∪ BY ∪ BS ∪ BFam)
    have h5 : (3/4 : ℝ) * Real.exp (-(8*qV r ε' θ D * (Fintype.card V:ℝ))) - 1/16
        ≤ (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (⋂ i, (A i)ᶜ)
          - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (BX ∪ BY ∪ BS ∪ BFam) := by
      linarith [hUB, hGprob]
    have h6 : (0:ℝ) < (3/4) * Real.exp (-(8*qV r ε' θ D * (Fintype.card V:ℝ))) - 1/16 := by
      nlinarith [hexphalf]
    calc (0:ℝ) < (3/4) * Real.exp (-(8*qV r ε' θ D * (Fintype.card V:ℝ))) - 1/16 := h6
      _ ≤ (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (⋂ i, (A i)ᶜ)
            - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob (BX ∪ BY ∪ BS ∪ BFam) := h5
      _ ≤ (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).prob
            ((⋂ i, (A i)ᶜ) \ (BX ∪ BY ∪ BS ∪ BFam)) := h3
  obtain ⟨ω, hω⟩ := FinProb.exists_of_prob_pos _ hcombo
  obtain ⟨hωA, hωnot⟩ := hω
  rw [Set.mem_union, Set.mem_union, Set.mem_union, not_or, not_or, not_or] at hωnot
  obtain ⟨⟨⟨hBX', hBY'⟩, hBS'⟩, hFam'⟩ := hωnot
  refine ⟨ω, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have hNc : (𝓖.ncard : ℝ) = (Nat.card 𝓖 : ℝ) := by
      have h : 𝓖.ncard = Nat.card 𝓖 := by simp [Nat.card_eq_fintype_card]
      rw [h]
    simp only [BX, Set.mem_setOf_eq, not_lt] at hBX'
    rw [kept_card, hNc]
    exact hBX'
  · have hY := hYmean hp0 hp1
    have hsum := covF_card_add_uncovF_card 𝓖 ω
    have hcov := covX_ncard_eq 𝓖 ω
    have hle : (uncovF 𝓖 ω).card ≤ Fintype.card V := by omega
    have hcast : ((covF 𝓖 ω).card : ℝ) = (Fintype.card V : ℝ) - ((uncovF 𝓖 ω).card : ℝ) := by
      have h2 : (covF 𝓖 ω).card = Fintype.card V - (uncovF 𝓖 ω).card := by omega
      rw [h2, Nat.cast_sub hle]
    have hpt : (Fintype.card V : ℝ) - ((uncovF 𝓖 ω).card : ℝ)
          - (1 - Real.exp (-θ)) * (Fintype.card V : ℝ)
        = Real.exp (-θ) * (Fintype.card V : ℝ) - ((uncovF 𝓖 ω).card : ℝ) := by ring
    simp only [BY, Set.mem_setOf_eq, not_lt] at hBY'
    rw [hcov, hcast, hpt, abs_sub_comm]
    have htri := abs_sub_le ((uncovF 𝓖 ω).card : ℝ)
      ((edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp (fun ω => ((uncovF 𝓖 ω).card : ℝ)))
      (Real.exp (-θ) * (Fintype.card V : ℝ))
    linarith [htri, hY, hBY']
  · have hS := hSmean hp0 hp1
    simp only [BS, Set.mem_setOf_eq, not_lt] at hBS'
    linarith [hS, hBS']
  · intro v hv
    have hAv : ω ∈ (A v)ᶜ := Set.mem_iInter.mp hωA v
    simp only [A, Set.mem_compl_iff, Set.mem_setOf_eq, not_and, not_lt] at hAv
    exact hAv hv
  · -- per-set uncovered clause
    intro S hS
    have hnot : ¬ (δ / 2 * (S.card : ℝ) ≤ ((uncovFam 𝓖 ω S : ℕ) : ℝ)
        - (edgeMeasure 𝓖 (θ/(D:ℝ)) hp0 hp1).exp
            (fun ω => ((uncovFam 𝓖 ω S : ℕ) : ℝ))) := fun hc =>
      hFam' (Or.inl (Set.mem_iUnion₂.mpr ⟨S, hS, hc⟩))
    have hlt := not_le.mp hnot
    have hmean := hYfammean S hS hp0 hp1
    have hup := (abs_le.mp hmean).2
    linarith
  · -- per-set waste clause
    intro S hS
    by_contra hcon
    have hc : (1 + δ) * (2 * (r:ℝ) * θ ^ 2) * (S.card : ℝ) < ((badSum 𝓖 ω S : ℕ) : ℝ) :=
      not_le.mp hcon
    exact hFam' (Or.inr (Set.mem_iUnion₂.mpr ⟨S, hS, hc⟩))

end Work.Deep.Nibble
