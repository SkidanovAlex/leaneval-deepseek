import Submission.Work.Deep.Nibble.nibble_step
import Submission.Work.Deep.Nibble.log_one_sub_bound

set_option autoImplicit false
open scoped BigOperators

/-!
# Iterating the one-round nibble

`nibble_iter` iterates the one-round lemma `nibble_step` `T` times, maintaining the set of
still-uncovered vertices `U`, the matching `M` found so far, and the accumulated waste `Acc`.
The invariant (`IterInv`) records: everything is covered by `U ∪ ⋃₀M ∪ Acc`; `M` lies
outside `U`; `M` is a matching of `r`-sets; the degrees in `U` are `(1 ± εs j)·lev j`; `U`
shrinks geometrically; and the waste accumulates geometrically.

The arithmetic helpers at the end (`sum_geom_le`, `final_bound`, `nibble_ED`) are the
estimates used by `nibble_main` to turn the invariant at round `T` into the final bound.
-/

namespace Work.Deep.Nibble

variable {n : ℕ}

/-! ## Small arithmetic helpers -/

theorem nonneg4 {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ a * b * c * d :=
  mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc) hd

theorem nonneg5 {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) : 0 ≤ a * b * c * d * e :=
  mul_nonneg (nonneg4 ha hb hc hd) he

theorem sum_range_le_succ {f : ℕ → ℝ} (hnn : ∀ i, 0 ≤ f i) (j : ℕ) :
    (∑ i ∈ Finset.range j, f i) ≤ (∑ i ∈ Finset.range (j + 1), f i) := by
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (hnn j)

/-- `deg` on `univ` is `hd`. -/
theorem deg_univ (𝓗 : Set (Set (Fin n))) (v : Fin n) : deg 𝓗 Set.univ v = hd 𝓗 v := by
  rw [hd_eq_ncard, deg, star]
  congr 1
  ext s
  constructor
  · rintro ⟨-, hs, hv⟩; exact ⟨hs, hv⟩
  · rintro ⟨hs, hv⟩; exact ⟨Set.subset_univ _, hs, hv⟩

/-- The state invariant of the nibble iteration at round `j`.  `U` is the set of vertices
still uncovered (its degrees lie within `(1 ± εs j)` of the level `lev j`), `M` is the
matching of kept edges found so far, and `Acc` collects the vertices already discarded. -/
def IterInv (𝓗 : Set (Set (Fin n))) (r : ℕ) (θ δ lam : ℝ) (lev : ℕ → ℕ) (εs : ℕ → ℝ)
    (j : ℕ) (U Acc : Set (Fin n)) (M : Set (Set (Fin n))) : Prop :=
  Set.univ ⊆ U ∪ ⋃₀ M ∪ Acc ∧
  (⋃₀ M) ∩ U = ∅ ∧
  M ⊆ 𝓗 ∧
  (∀ e ∈ M, e.ncard = r) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
  (∀ v ∈ U, (deg 𝓗 U v : ℝ) ≤ (1 + εs j) * (lev j : ℝ) ∧
      (lev j : ℝ) ≤ (deg 𝓗 U v : ℝ)) ∧
  ((U.ncard : ℝ) ≤ (n : ℝ) * lam^j) ∧
  ((Acc.ncard : ℝ) ≤ (n : ℝ) * (r : ℝ) * (1 + δ) * (θ - θ * Real.exp (-θ)) *
      (∑ i ∈ Finset.range j, lam^i))

/-- **Iteration of the one-round nibble.**  Starting from the full vertex set with levels
`lev`, `T` rounds produce a matching covering all but `n·lam^T + (waste)`. -/
theorem nibble_iter {r : ℕ} (hr : 2 ≤ r) {θ δ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ θ / 100) (hlam0 : 0 ≤ lam)
    (hlamdef : lam = (1 + 2 * δ) * Real.exp (-θ)) {T : ℕ}
    {lev : ℕ → ℕ} {εs εs' : ℕ → ℝ}
    (hεs0 : ∀ j, 0 < εs j) (hεs1 : ∀ j < T, εs j ≤ θ / 100)
    (hεsδ : ∀ j < T, 4 * εs j ≤ δ)
    (hεs'0 : ∀ j, 0 < εs' j) (hεs'1 : ∀ j < T, εs' j ≤ 1 / 2)
    (hεs'2 : ∀ j < T, 100 * (εs j + εs j * (r : ℝ) * θ) ≤ εs' j)
    (hεs'six : ∀ j < T, εs' j ≤ 1 / 6)
    (hεseq : ∀ j < T, εs (j + 1) = 8 * εs' j)
    (hlevstep : ∀ j < T, lev (j + 1) = nextD r θ (lev j) (εs' j))
    {Dmin : ℕ → ℕ} (hDmin1 : ∀ j < T, 1 ≤ Dmin j) (hminD : ∀ j < T, Dmin j ≤ lev j)
    (hround : ∀ j < T, ∀ {V : Type} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) (D' : ℕ),
        Dmin j ≤ D' → D' ≤ Fintype.card V → HLin 𝓖 → HUnif 𝓖 r →
        (∀ v : V, |((hd 𝓖 v : ℝ)) - (D' : ℝ)| ≤ εs j * (D' : ℝ)) →
        ∃ ω : 𝓖 → Bool, RoundGood 𝓖 r D' θ δ (εs' j) (rPred r θ D') ω)
    (hbig : ∀ j < T, 1 ≤ εs' j * rPred r θ (lev j))
    (𝓗 : Set (Set (Fin n))) (D0 : ℕ) (hl : HLin 𝓗) (hu : HUnif 𝓗 r)
    (hlev0 : lev 0 = D0)
    (hinit : ∀ v : Fin n, ((D0 : ℝ) ≤ (hd 𝓗 v : ℝ)) ∧
      ((hd 𝓗 v : ℝ) ≤ (1 + εs 0) * (D0 : ℝ))) :
    ∃ U Acc : Set (Fin n), ∃ M : Set (Set (Fin n)),
      IterInv 𝓗 r θ δ lam lev εs T U Acc M := by
  classical
  have key : ∀ j : ℕ, j ≤ T → ∃ U Acc : Set (Fin n), ∃ M : Set (Set (Fin n)),
      IterInv 𝓗 r θ δ lam lev εs j U Acc M := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨Set.univ, ∅, ∅, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        exact Or.inl (Or.inl hx)
      · rw [Set.sUnion_empty, Set.empty_inter]
      · intro s hs
        exact absurd hs (Set.notMem_empty s)
      · intro e he
        exact absurd he (Set.notMem_empty e)
      · intro e he
        exact absurd he (Set.notMem_empty e)
      · intro v _
        have hv := hinit v
        rw [hlev0, deg_univ]
        exact ⟨hv.2, hv.1⟩
      · have h1 : (Set.univ : Set (Fin n)).ncard = n := by
          rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
        rw [h1, pow_zero, mul_one]
      · have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.range 0, lam ^ i :=
          Finset.sum_nonneg (fun i _ => pow_nonneg hlam0 i)
        have hexp : (0 : ℝ) ≤ θ - θ * Real.exp (-θ) := by
          have h2 : Real.exp (-θ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          nlinarith [hθ0]
        rw [Set.ncard_empty, Nat.cast_zero]
        exact nonneg5 (Nat.cast_nonneg n) (Nat.cast_nonneg r) (by linarith) hexp hsum
    | succ j ih =>
      intro hj
      obtain ⟨U, Acc, M, hinv⟩ := ih (by omega)
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hinv
      have hj' : j < T := by omega
      by_cases hU : U = ∅
      · refine ⟨U, Acc, M, ?_⟩
        refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_⟩
        · intro v hv
          rw [hU] at hv
          exact absurd hv (Set.notMem_empty v)
        · have h1 : U.ncard = 0 := by rw [hU, Set.ncard_empty]
          rw [h1, Nat.cast_zero]
          exact mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hlam0 (j + 1))
        · calc (Acc.ncard : ℝ)
              ≤ (n : ℝ) * (r : ℝ) * (1 + δ) * (θ - θ * Real.exp (-θ))
                  * (∑ i ∈ Finset.range j, lam ^ i) := h8
            _ ≤ (n : ℝ) * (r : ℝ) * (1 + δ) * (θ - θ * Real.exp (-θ))
                  * (∑ i ∈ Finset.range (j + 1), lam ^ i) := by
                refine mul_le_mul_of_nonneg_left ?_ (nonneg4 (Nat.cast_nonneg n)
                  (Nat.cast_nonneg r) (by linarith) ?_)
                · exact sum_range_le_succ (fun i => pow_nonneg hlam0 i) j
                · have h2 : Real.exp (-θ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
                  nlinarith [hθ0]
      · obtain ⟨v0, hv0⟩ := Set.nonempty_iff_ne_empty.mpr hU
        have hlevdeg : lev j ≤ deg 𝓗 U v0 := by
          exact_mod_cast (h6 v0 hv0).2
        have hdegnat : deg 𝓗 U v0 ≤ (r - 1) * deg 𝓗 U v0 :=
          Nat.le_mul_of_pos_left _ (by omega)
        have hDcard : lev j ≤ U.ncard := by
          have h9 := deg_le_card hl hu hv0
          omega
        obtain ⟨ω, hU'sub, hupper, hlower, hcard, hwaste, hMsub, hMuni, hMdisj, hMsubU'⟩ :=
          nibble_step (D := lev j) (ε := εs j) (ε' := εs' j) (Dmin := Dmin j)
            hr hθ0 hθ1 hδ0 hδ1 (hεs0 j) (hεs1 j hj') (hεsδ j hj')
            (hεs'0 j) (hεs'1 j hj') (hεs'2 j hj') (hDmin1 j hj') (hminD j hj') (hround j hj')
            hl hu hDcard (fun v hv => (h6 v hv).1) (fun v hv => (h6 v hv).2)
            (hbig j hj') (hεs'six j hj')
        set U' : Set (Fin n) := rU' 𝓗 U ω with hU'def
        set M' : Set (Set (Fin n)) := M ∪ rM 𝓗 U ω with hM'def
        set Acc' : Set (Fin n) := Acc ∪ (U \ (U' ∪ ⋃₀ (rM 𝓗 U ω))) with hAcc'def
        refine ⟨U', Acc', M', ?_⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- containment
          intro x hx
          rcases h1 hx with (hxU | hxM) | hxAcc
          · by_cases hxU' : x ∈ U'
            · exact Or.inl (Or.inl hxU')
            · by_cases hxrM : x ∈ ⋃₀ (rM 𝓗 U ω)
              · refine Or.inl (Or.inr ?_)
                rw [hM'def, Set.sUnion_union]
                exact Or.inr hxrM
              · refine Or.inr (Or.inr ?_)
                exact ⟨hxU, fun hc => hc.elim hxU' hxrM⟩
          · refine Or.inl (Or.inr ?_)
            rw [hM'def, Set.sUnion_union]
            exact Or.inl hxM
          · exact Or.inr (Or.inl hxAcc)
        · -- the matching lies outside `U'`
          rw [hM'def, Set.sUnion_union]
          rw [Set.eq_empty_iff_forall_notMem]
          rintro x ⟨hxm, hxU'⟩
          rcases hxm with hxM | hxrM
          · have hthis : x ∈ (⋃₀ M) ∩ U := ⟨hxM, hU'sub hxU'⟩
            rw [h2] at hthis
            exact hthis
          · exact (hMsubU' hxrM).2 hxU'
        · exact Set.union_subset h3 hMsub
        · rintro e (he | he)
          · exact h4 e he
          · exact hMuni e he
        · rintro e (he | he) f (hf | hf) hef
          · exact h5 e he f hf hef
          · rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
            rintro x ⟨hxe, hxf⟩
            have hxUn : x ∈ U := (hMsubU' ⟨f, hf, hxf⟩).1
            have hthis : x ∈ (⋃₀ M) ∩ U := ⟨⟨e, he, hxe⟩, hxUn⟩
            rw [h2] at hthis
            exact hthis
          · rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
            rintro x ⟨hxe, hxf⟩
            have hxUn : x ∈ U := (hMsubU' ⟨e, he, hxe⟩).1
            have hthis : x ∈ (⋃₀ M) ∩ U := ⟨⟨f, hf, hxf⟩, hxUn⟩
            rw [h2] at hthis
            exact hthis
          · exact hMdisj e he f hf hef
        · -- the degree invariant
          intro v hv
          have hup : (deg 𝓗 U' v : ℝ) ≤ (1 + 8 * εs' j) * (nextD r θ (lev j) (εs' j) : ℝ) :=
            hupper v hv
          have hlo : (nextD r θ (lev j) (εs' j) : ℝ) ≤ (deg 𝓗 U' v : ℝ) := hlower v hv
          constructor
          · show (deg 𝓗 U' v : ℝ) ≤ (1 + εs (j + 1)) * ((lev (j + 1) : ℕ) : ℝ)
            rw [hεseq j hj', hlevstep j hj']
            exact hup
          · show ((lev (j + 1) : ℕ) : ℝ) ≤ (deg 𝓗 U' v : ℝ)
            rw [hlevstep j hj']
            exact hlo
        · -- the residual set shrinks geometrically
          calc (U'.ncard : ℝ) ≤ (1 + 2 * δ) * Real.exp (-θ) * (U.ncard : ℝ) := hcard
            _ ≤ (1 + 2 * δ) * Real.exp (-θ) * ((n : ℝ) * lam ^ j) :=
                mul_le_mul_of_nonneg_left h7 (by positivity)
            _ = (n : ℝ) * lam ^ (j + 1) := by rw [hlamdef, pow_succ]; ring
        · -- the accumulated waste
          have hexp : (0 : ℝ) ≤ θ - θ * Real.exp (-θ) := by
            have h2 : Real.exp (-θ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
            nlinarith [hθ0]
          have hCnn : (0 : ℝ) ≤ (r : ℝ) * (1 + δ) * (θ - θ * Real.exp (-θ)) :=
            mul_nonneg (mul_nonneg (Nat.cast_nonneg r) (by linarith)) hexp
          have hsub : (Acc'.ncard : ℝ)
              ≤ (Acc.ncard : ℝ) + ((U \ (U' ∪ ⋃₀ (rM 𝓗 U ω))).ncard : ℝ) := by
            rw [hAcc'def]
            exact_mod_cast Set.ncard_union_le Acc (U \ (U' ∪ ⋃₀ (rM 𝓗 U ω)))
          calc (Acc'.ncard : ℝ)
              ≤ (Acc.ncard : ℝ) + ((U \ (U' ∪ ⋃₀ (rM 𝓗 U ω))).ncard : ℝ) := hsub
            _ ≤ (n : ℝ) * (r : ℝ) * (1 + δ) * (θ - θ * Real.exp (-θ))
                  * (∑ i ∈ Finset.range j, lam ^ i)
                + (r : ℝ) * (1 + δ) * (θ - θ * Real.exp (-θ)) * (U.ncard : ℝ) :=
                add_le_add h8 hwaste
            _ ≤ (n : ℝ) * (r : ℝ) * (1 + δ) * (θ - θ * Real.exp (-θ))
                  * (∑ i ∈ Finset.range j, lam ^ i)
                + (r : ℝ) * (1 + δ) * (θ - θ * Real.exp (-θ)) * ((n : ℝ) * lam ^ j) := by
                have hw : (r : ℝ) * (1 + δ) * (θ - θ * Real.exp (-θ)) * (U.ncard : ℝ)
                    ≤ (r : ℝ) * (1 + δ) * (θ - θ * Real.exp (-θ)) * ((n : ℝ) * lam ^ j) :=
                  mul_le_mul_of_nonneg_left h7 hCnn
                linarith [hw]
            _ = (n : ℝ) * (r : ℝ) * (1 + δ) * (θ - θ * Real.exp (-θ))
                  * (∑ i ∈ Finset.range (j + 1), lam ^ i) := by
                rw [Finset.sum_range_succ]; ring
  obtain ⟨U, Acc, M, h⟩ := key T le_rfl
  exact ⟨U, Acc, M, h⟩

/-- The geometric series bound used at the end of the iteration. -/
theorem sum_geom_le {T : ℕ} {lam θ : ℝ} (hθ0 : 0 < θ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hl : θ / 4 ≤ 1 - lam) : (∑ i ∈ Finset.range T, lam ^ i) ≤ 4 / θ := by
  have hSnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range T, lam ^ i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg h0 i)
  have hgeom : (∑ i ∈ Finset.range T, lam ^ i) * (1 - lam) = 1 - lam ^ T := by
    have h := geom_sum_mul lam T
    have h2 : (∑ i ∈ Finset.range T, lam ^ i) * (1 - lam)
        = -((∑ i ∈ Finset.range T, lam ^ i) * (lam - 1)) := by ring
    rw [h2, h]
    ring
  have h2 : lam ^ T ≤ 1 := pow_le_one₀ h0 h1
  have h2' : (0 : ℝ) ≤ lam ^ T := pow_nonneg h0 T
  have h3 : (∑ i ∈ Finset.range T, lam ^ i) * (θ / 4) ≤ 1 := by
    calc (∑ i ∈ Finset.range T, lam ^ i) * (θ / 4)
        ≤ (∑ i ∈ Finset.range T, lam ^ i) * (1 - lam) := mul_le_mul_of_nonneg_left hl hSnn
      _ = 1 - lam ^ T := hgeom
      _ ≤ 1 := by linarith
  rw [le_div_iff₀ hθ0]
  linarith

/-- The final numerical estimate. -/
theorem final_bound {T : ℕ} {n γ r θ δ lam : ℝ} (hn : 0 ≤ n) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1 / 100) (hδ0 : 0 < δ) (hδ1 : δ ≤ θ / 100) (hr0 : 0 ≤ r)
    (hrθ : r * θ ≤ γ / 20) (hlamT : lam ^ T ≤ γ / 2) :
    n * lam ^ T + n * (r * (1 + δ) * (θ - θ * Real.exp (-θ)) * (4 / θ)) ≤ γ * n := by
  have hE : Real.exp (-θ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h1 : n * lam ^ T ≤ n * (γ / 2) := mul_le_mul_of_nonneg_left hlamT hn
  have h4 : r * (1 + δ) * (θ - θ * Real.exp (-θ)) * (4 / θ) ≤ γ / 2 := by
    have hkey : (θ - θ * Real.exp (-θ)) * (4 / θ) = 4 * (1 - Real.exp (-θ)) := by
      field_simp
    have hC : r * (1 + δ) * (θ - θ * Real.exp (-θ)) * (4 / θ)
        = 4 * (1 + δ) * (r * (1 - Real.exp (-θ))) := by
      rw [show r * (1 + δ) * (θ - θ * Real.exp (-θ)) * (4 / θ)
          = (r * (1 + δ)) * ((θ - θ * Real.exp (-θ)) * (4 / θ)) by ring, hkey]
      ring
    rw [hC]
    have h1e : 1 - Real.exp (-θ) ≤ θ := by
      have := Real.add_one_le_exp (-θ)
      linarith
    have h2 : r * (1 - Real.exp (-θ)) ≤ r * θ :=
      mul_le_mul_of_nonneg_left h1e hr0
    have h3 : (1 + δ) ≤ 5 / 2 := by linarith
    have h5 : 4 * (1 + δ) ≤ 4 * (5 / 2) := mul_le_mul_of_nonneg_left h3 (by norm_num)
    have h7nn : 0 ≤ r * θ := mul_nonneg hr0 hθ0.le
    calc 4 * (1 + δ) * (r * (1 - Real.exp (-θ)))
        ≤ 4 * (1 + δ) * (r * θ) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ ≤ 4 * (5 / 2) * (r * θ) := mul_le_mul_of_nonneg_right h5 h7nn
      _ ≤ 4 * (5 / 2) * (γ / 20) := mul_le_mul_of_nonneg_left hrθ (by norm_num)
      _ = γ / 2 := by ring
  calc n * lam ^ T + n * (r * (1 + δ) * (θ - θ * Real.exp (-θ)) * (4 / θ))
      ≤ n * (γ / 2) + n * (γ / 2) := add_le_add h1 (mul_le_mul_of_nonneg_left h4 hn)
    _ = γ * n := by ring

/-- The exponent bound that lets the iteration start: once `D ≥ (1/ε0)·32·W·A` with
`q^T·W = 1`, the initial accuracy dominates the level shift `A`. -/
theorem nibble_ED {T : ℕ} {A W q D D0 ε0 K : ℝ}
    (hW : 0 < W) (hqW : q ^ T * W = 1) (hε0 : 0 < ε0) (hA : 0 ≤ A)
    (hD : (1 / ε0) * 32 * W * A ≤ D) (hD0 : D / 2 ≤ D0) (hK : 1 ≤ K) :
    A ≤ K * ε0 * (D0 * q ^ T) := by
  have hstar : 32 * W * A ≤ ε0 * D := by
    have hmul : ε0 * ((1 / ε0) * 32 * W * A) = 32 * W * A := by field_simp
    calc 32 * W * A = ε0 * ((1 / ε0) * 32 * W * A) := hmul.symm
      _ ≤ ε0 * D := mul_le_mul_of_nonneg_left hD hε0.le
  have hD2 : 16 * W * A ≤ ε0 * (D / 2) := by
    have h := mul_le_mul_of_nonneg_right hstar (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc 16 * W * A = 32 * W * A * (1 / 2) := by ring
      _ ≤ ε0 * D * (1 / 2) := h
      _ = ε0 * (D / 2) := by ring
  have hD0' : 16 * W * A ≤ ε0 * D0 := by
    calc 16 * W * A ≤ ε0 * (D / 2) := hD2
      _ ≤ ε0 * D0 := mul_le_mul_of_nonneg_left hD0 hε0.le
  have hDnn : (0 : ℝ) ≤ D := le_trans (by positivity : (0:ℝ) ≤ (1/ε0) * 32 * W * A) hD
  have hD0nn : (0 : ℝ) ≤ D0 := by linarith
  have hqT : q ^ T = 1 / W := (eq_div_iff (ne_of_gt hW)).mpr hqW
  have hqTnn : (0 : ℝ) ≤ q ^ T := by rw [hqT]; positivity
  have hfin : 16 * A ≤ ε0 * (D0 * q ^ T) := by
    rw [hqT]
    have hmul : ε0 * (D0 * (1 / W)) = ε0 * D0 / W := by ring
    rw [hmul, le_div_iff₀ hW]
    calc 16 * A * W = 16 * W * A := by ring
      _ ≤ ε0 * D0 := hD0'
  have hXnn : (0 : ℝ) ≤ ε0 * (D0 * q ^ T) := mul_nonneg hε0.le (mul_nonneg hD0nn hqTnn)
  calc A ≤ 16 * A := by linarith
    _ ≤ ε0 * (D0 * q ^ T) := hfin
    _ ≤ K * (ε0 * (D0 * q ^ T)) := by
        have h := mul_le_mul_of_nonneg_right hK hXnn
        rwa [one_mul] at h
    _ = K * ε0 * (D0 * q ^ T) := by ring

end Work.Deep.Nibble
