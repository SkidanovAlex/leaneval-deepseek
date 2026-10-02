import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.FamEst

/-!
# The uncovered-count tail bound of one wasteful round

This module proves `Work.Deep.Nibble.r2_Yfam_tail`: the concentration of the number
`uncovFam 𝓖 ω S` of vertices of `S` left uncovered by one round, around its mean.

The certificate argument is the one described in the paper's nibble (and in the
session notes of `Deep/Nibble`):  the certificate of an outcome `ω` is

* the set `I` of one chosen kept edge through every *covered* vertex of `S`
  (`certU`), of size at most `|S|`;

a vertex `v ∈ S` that is uncovered in `ω'` but covered in `ω` has its chosen edge
`e_v ∈ I` kept in `ω` and unkept in `ω'` (otherwise `v` would be covered in `ω'`),
so that `e_v` is a disagreement between `ω` and `ω'` on `I`;  since `e_v ∋ v` and
every edge has `r` vertices, a single disagreement can serve at most `r` vertices.
Hence every newly uncovered vertex carries a disagreement, with at most `r` vertices
per disagreement, and the Bruhn--Joos inequality `bj_talagrand` with `c = r` and
certificate size `s = |S|` gives the claimed tail.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The certificate of the uncovered count -/

/-- A chosen kept edge through `v` (a junk value `e₀` when there is none). -/
noncomputable def witU (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (e₀ : 𝓖) (v : V) : 𝓖 := by
  classical
  exact if h : ∃ e : 𝓖, ω e = true ∧ v ∈ (e : Set V) then Classical.choose h else e₀

lemma witU_spec {𝓖 : Set (Set V)} {ω : 𝓖 → Bool} {e₀ : 𝓖} {v : V}
    (h : ∃ e : 𝓖, ω e = true ∧ v ∈ (e : Set V)) :
    ω (witU 𝓖 ω e₀ v) = true ∧ v ∈ (witU 𝓖 ω e₀ v : Set V) := by
  classical
  rw [witU, dif_pos h]
  exact Classical.choose_spec h

/-- The certificate of an outcome `ω`: one chosen kept edge through every covered
vertex of `S`. -/
noncomputable def certU (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (e₀ : 𝓖) (S : Finset V) :
    Finset 𝓖 := by
  classical
  exact (S.filter (fun v => v ∈ covX 𝓖 ω)).image (fun v => witU 𝓖 ω e₀ v)

lemma certU_card_le (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (e₀ : 𝓖) (S : Finset V) :
    (certU 𝓖 ω e₀ S).card ≤ S.card := by
  classical
  rw [certU]
  exact le_trans Finset.card_image_le (Finset.card_filter_le S _)

/-! ## The certificate inequality -/

/-- Passing from `ω` to `ω'`, at most `r` vertices of `S` become newly uncovered per
disagreement on the certificate `certU 𝓖 ω e₀ S`. -/
lemma uncovFam_cert {𝓖 : Set (Set V)} {r : ℕ} (hr1 : 1 ≤ r) (huni : HUnif 𝓖 r)
    (e₀ : 𝓖) (S : Finset V) (ω ω' : 𝓖 → Bool) {u : ℝ}
    (hlt : (((certU 𝓖 ω e₀ S).filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / (r : ℝ)) :
    ((uncovFam 𝓖 ω' S : ℕ) : ℝ) < ((uncovFam 𝓖 ω S : ℕ) : ℝ) + u := by
  classical
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  set disI : Finset 𝓖 := (certU 𝓖 ω e₀ S).filter (fun i => ω i ≠ ω' i) with hdisI
  have hlt' : (disI.card : ℝ) < u / (r : ℝ) := by rw [hdisI]; exact hlt
  set A : Finset V := S.filter (fun v => v ∉ covX 𝓖 ω) with hAdef
  set B : Finset V := S.filter (fun v => v ∉ covX 𝓖 ω' ∧ v ∈ covX 𝓖 ω) with hBdef
  have hAeq : A.card = uncovFam 𝓖 ω S := by rw [hAdef, uncovFam]
  have hBfilter : (S.filter (fun v => v ∉ covX 𝓖 ω')).card = uncovFam 𝓖 ω' S := by
    rw [uncovFam]
  -- Step 1: the uncovered set in `ω'` is contained in `A ∪ B`.
  have hsub : (S.filter (fun v => v ∉ covX 𝓖 ω')) ⊆ A ∪ B := by
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvS, hvU'⟩ := hv
    by_cases hcov : v ∈ covX 𝓖 ω
    · exact Finset.mem_union.mpr (Or.inr (by
        rw [hBdef, Finset.mem_filter]; exact ⟨hvS, hvU', hcov⟩))
    · exact Finset.mem_union.mpr (Or.inl (by
        rw [hAdef, Finset.mem_filter]; exact ⟨hvS, hcov⟩))
  have hNle : (S.filter (fun v => v ∉ covX 𝓖 ω')).card ≤ A.card + B.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  -- Step 2: every newly uncovered vertex carries a disagreement, with at most `r`
  -- vertices per disagreement.
  have hmaps : Set.MapsTo (witU 𝓖 ω e₀) ↑B ↑disI := by
    intro v hv
    rw [Finset.mem_coe, hBdef, Finset.mem_filter] at hv
    obtain ⟨hvS, hvU', hcov⟩ := hv
    have hspec := witU_spec (e₀ := e₀) ((mem_covX_iff 𝓖 ω v).mp hcov)
    have hmemcert : witU 𝓖 ω e₀ v ∈ certU 𝓖 ω e₀ S := by
      rw [certU]
      exact Finset.mem_image.mpr ⟨v, by rw [Finset.mem_filter]; exact ⟨hvS, hcov⟩, rfl⟩
    have hne : ω (witU 𝓖 ω e₀ v) ≠ ω' (witU 𝓖 ω e₀ v) := by
      intro heq
      have htrue' : ω' (witU 𝓖 ω e₀ v) = true := by rw [← heq]; exact hspec.1
      exact hvU' ((mem_covX_iff 𝓖 ω' v).mpr ⟨witU 𝓖 ω e₀ v, htrue', hspec.2⟩)
    rw [Finset.mem_coe, hdisI, Finset.mem_filter]
    exact ⟨hmemcert, hne⟩
  have hBcard : B.card ≤ disI.card * r := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc ∑ i ∈ disI, (B.filter (fun v => witU 𝓖 ω e₀ v = i)).card
        ≤ ∑ _i ∈ disI, r := Finset.sum_le_sum (fun i _ => by
            have hle : B.filter (fun v => witU 𝓖 ω e₀ v = i) ⊆ eFin 𝓖 i := by
              intro v hv
              rw [Finset.mem_filter] at hv
              obtain ⟨hvB, hwv⟩ := hv
              rw [hBdef, Finset.mem_filter] at hvB
              obtain ⟨-, -, hcov⟩ := hvB
              have hspec := witU_spec (e₀ := e₀) ((mem_covX_iff 𝓖 ω v).mp hcov)
              rw [hwv] at hspec
              exact (eFin_mem_iff 𝓖).mpr hspec.2
            calc (B.filter (fun v => witU 𝓖 ω e₀ v = i)).card ≤ (eFin 𝓖 i).card :=
                  Finset.card_le_card hle
              _ = r := eFin_card_of_hunif huni i)
      _ = disI.card * r := by rw [Finset.sum_const, smul_eq_mul]
  -- Step 3: arithmetic.
  have hBreal : ((B.card : ℕ) : ℝ) < u := by
    have h1 : ((B.card : ℕ) : ℝ) ≤ (disI.card : ℝ) * (r : ℝ) := by
      have h1' : ((B.card : ℕ) : ℝ) ≤ ((disI.card * r : ℕ) : ℝ) := by exact_mod_cast hBcard
      have h2 : ((disI.card * r : ℕ) : ℝ) = (disI.card : ℝ) * (r : ℝ) := by push_cast; ring
      linarith [h1']
    have h3 : (disI.card : ℝ) * (r : ℝ) < u := by
      rw [mul_comm]
      calc (r : ℝ) * (disI.card : ℝ) < (r : ℝ) * (u / (r : ℝ)) :=
            mul_lt_mul_of_pos_left hlt' hrR
        _ = u := mul_div_cancel₀ u (ne_of_gt hrR)
    linarith
  have hNcast : ((S.filter (fun v => v ∉ covX 𝓖 ω')).card : ℝ)
      ≤ (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hNle
  have hAr : ((A.card : ℕ) : ℝ) = ((uncovFam 𝓖 ω S : ℕ) : ℝ) := by rw [hAeq]
  have hNr : ((S.filter (fun v => v ∉ covX 𝓖 ω')).card : ℝ)
      = ((uncovFam 𝓖 ω' S : ℕ) : ℝ) := by rw [hBfilter]
  have hgoal : ((S.filter (fun v => v ∉ covX 𝓖 ω')).card : ℝ) < (A.card : ℝ) + u := by
    linarith
  rw [hAr] at hgoal
  rwa [hNr] at hgoal

/-! ## The degenerate case of a constant variable -/

/-- A random variable constant on all outcomes deviates from its mean by nothing. -/
private lemma prob_le_of_const {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) (X : Ω → ℝ) (c : ℝ)
    (hX : X = fun _ => c) {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C) :
    μ.prob {ω | t ≤ |X ω - μ.exp X|} ≤ C := by
  classical
  have hexp : μ.exp X = c := by rw [hX, FinProb.exp_const]
  have hempty : {ω | t ≤ |X ω - μ.exp X|} = ∅ := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    have h1 : X ω = c := congr_fun hX ω
    rw [hexp, h1, sub_self, abs_zero]
    exact not_le.mpr ht
  rw [hempty, FinProb.prob_empty]
  exact hC

/-! ## The tail bound -/

theorem r2_Yfam_tail {V : Type*} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) {r : ℕ}
    (hr : 2 ≤ r) (huni : Work.Deep.Nibble.HUnif 𝓖 r) {θ : ℝ} (hθ0 : 0 < θ) {D : ℕ}
    (hD : 1 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) < 1) (S : Finset V) {t : ℝ}
    (ht : 50 * (r : ℝ) * Real.sqrt (S.card : ℝ) < t) :
    (Work.Deep.Nibble.edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).prob
        {ω : 𝓖 → Bool | t ≤ |((Work.Deep.Nibble.uncovFam 𝓖 ω S : ℕ) : ℝ)
          - (Work.Deep.Nibble.edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).exp
              (fun ω => ((Work.Deep.Nibble.uncovFam 𝓖 ω S : ℕ) : ℝ))|}
      ≤ 4 * Real.exp (- t ^ 2 / (16 * (r : ℝ) ^ 2 * (S.card : ℝ))) := by
  classical
  have hr1 : 1 ≤ r := by omega
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hp_pos : 0 < θ / (D : ℝ) := div_pos hθ0 hDpos
  have htpos : 0 < t := by
    have h1 : (0 : ℝ) ≤ Real.sqrt (S.card : ℝ) := Real.sqrt_nonneg _
    nlinarith [ht, hrR, h1]
  have htarget : (0 : ℝ) ≤ 4 * Real.exp (- t ^ 2 / (16 * (r : ℝ) ^ 2 * (S.card : ℝ))) :=
    mul_nonneg (by norm_num) (Real.exp_pos _).le
  rcases Nat.eq_zero_or_pos S.card with hS0 | hSpos
  · -- `S = ∅`: the variable vanishes identically.
    have hSempty : S = ∅ := Finset.card_eq_zero.mp hS0
    have hX : (fun ω : 𝓖 → Bool => ((uncovFam 𝓖 ω S : ℕ) : ℝ)) = fun _ => 0 := by
      funext ω
      have hz : uncovFam 𝓖 ω S = 0 := by rw [uncovFam, hSempty]; simp
      rw [hz]; simp
    exact prob_le_of_const _ _ 0 hX htpos htarget
  · -- `S.card ≥ 1`, so `V` is nonempty.
    have hVne : Nonempty V := by
      obtain ⟨v, -⟩ := Finset.card_pos.mp hSpos
      exact ⟨v⟩
    have hM : 1 ≤ (Fintype.card V : ℝ) := by
      have h : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hVne
      exact_mod_cast h
    have hsup : ∀ ω : 𝓖 → Bool, |((uncovFam 𝓖 ω S : ℕ) : ℝ)| ≤ (Fintype.card V : ℝ) := by
      intro ω
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      have h1 : ((uncovFam 𝓖 ω S : ℕ) : ℝ) ≤ (S.card : ℝ) := by
        have hle : uncovFam 𝓖 ω S ≤ S.card := by
          rw [uncovFam]; exact Finset.card_filter_le S _
        exact_mod_cast hle
      have h2 : (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast Finset.card_le_univ S
      linarith
    rcases Set.eq_empty_or_nonempty 𝓖 with hG | hG
    · -- `𝓖 = ∅`: every vertex of `S` is uncovered, the variable is `|S|`.
      have hcov0 : ∀ ω : 𝓖 → Bool, covX 𝓖 ω = ∅ := by
        intro ω
        have hkept : kept 𝓖 ω = ∅ := by
          ext e
          constructor
          · rintro ⟨he, -⟩
            rw [hG] at he
            simp at he
          · intro h
            simp at h
        rw [covX, hkept]; simp
      have huncov : ∀ ω : 𝓖 → Bool, uncovFam 𝓖 ω S = S.card := by
        intro ω
        rw [uncovFam,
          show S.filter (fun v => v ∉ covX 𝓖 ω) = S from
            Finset.filter_true_of_mem (fun v _ => by rw [hcov0 ω]; simp)]
      have hX : (fun ω : 𝓖 → Bool => ((uncovFam 𝓖 ω S : ℕ) : ℝ)) = fun _ => (S.card : ℝ) := by
        funext ω; rw [huncov ω]
      exact prob_le_of_const _ _ (S.card : ℝ) hX htpos htarget
    · -- The certificate argument.
      obtain ⟨e₀, he₀⟩ := hG
      let e₁ : 𝓖 := ⟨e₀, he₀⟩
      have hc : 1 ≤ (r : ℝ) := by exact_mod_cast hr1
      have hs : 1 ≤ S.card := hSpos
      have hfull : ∀ i : 𝓖, ∀ x : Bool,
          0 < ((fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le) i).wt x := by
        intro i x
        cases x with
        | true => simpa using hp_pos
        | false => simpa using (show (0 : ℝ) < 1 - θ / (D : ℝ) by linarith)
      have hexc : (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le)).prob
          (∅ : Set (𝓖 → Bool)) ≤ 1 / (Fintype.card V : ℝ) ^ 2 := by
        rw [FinProb.prob_empty]; positivity
      have hcert : ∀ u : ℝ, 0 < u → ∀ ω : 𝓖 → Bool, ω ∉ (∅ : Set (𝓖 → Bool)) →
          ∃ I : Finset 𝓖, I.card ≤ S.card ∧
            ∀ ω' : 𝓖 → Bool, ω' ∉ (∅ : Set (𝓖 → Bool)) →
              ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / (r : ℝ) →
                (fun ω : 𝓖 → Bool => ((uncovFam 𝓖 ω S : ℕ) : ℝ)) ω'
                  < (fun ω : 𝓖 → Bool => ((uncovFam 𝓖 ω S : ℕ) : ℝ)) ω + u := by
        intro u hu ω _
        refine ⟨certU 𝓖 ω e₁ S, certU_card_le 𝓖 ω e₁ S, fun ω' _ hlt => ?_⟩
        exact uncovFam_cert hr1 huni e₁ S ω ω' hlt
      have hgoal := bj_talagrand (μ := fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le) hfull
        (fun ω : 𝓖 → Bool => ((uncovFam 𝓖 ω S : ℕ) : ℝ)) (Fintype.card V : ℝ) hM hsup
        (r : ℝ) hc S.card hs (∅ : Set (𝓖 → Bool)) hexc hcert t ht
      rw [FinProb.prob_empty, mul_zero, add_zero] at hgoal
      simpa only [edgeMeasure] using hgoal

end Work.Deep.Nibble
