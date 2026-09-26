import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.PinchLemma3.ClosedDiscA.exists_alternating_partition
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq
import Submission.Work.PinchLemma3.ClosedDiscA.windingSpan_union_le_sup_of_isPathConnected_inter

/-!
# The winding span is subadditive over two pieces with a *grounded* intersection

`Work.PinchLemma3.ClosedDiscA.windingSpan_union_le_sup_of_grounded_inter`.

The sibling `windingSpan_union_le_sup_of_isPathConnected_inter` proves the subadditivity of the
winding span over two regions `A, B` open in the carrier whose *intersection* is path connected.
Here the hypothesis on the intersection is replaced by the weaker *grounding* condition

  `∀ x y ∈ A ∩ B, JoinedIn A x y → JoinedIn (A ∩ B) x y`

saying that two points of `A ∩ B` which can be joined inside `A` can be joined inside `A ∩ B`;
the second region `B` is assumed path connected.

The two form the same kind of statement, and the proof follows the same plan: a closed curve of
`A ∪ B` is decomposed into finitely many monochromatic arcs alternating between `A` and `B` whose
endpoints lie in `A ∩ B` (`exists_alternating_partition`); one has to produce, for each `A`-arc, a
"connector" in `A ∩ B` and then to combine the pieces into loops of `A` and of `B`.

The difference is *which* pieces can be closed up:

* the grounding condition produces, for every `A`-arc `a_j` (running from `b (2j)` to `b (2j+1)`),
  a path `e_j` inside `A ∩ B` with the same endpoints — so that `a_j · e_j⁻¹` is a loop *of `A`*,
  of vanishing `ψ`-displacement since the winding span of `A` vanishes.  Hence the displacement of
  `a_j` equals that of the path `e_j` inside `A ∩ B`;
* consequently the chain `e₀ · (B-arc₀) · e₁ · (B-arc₁) · … · e_{k-1} · (B-arc_{k-1})` runs
  through `A ∩ B ⊆ B` and through `B`, closes up because the last endpoint of the alternating
  partition is again its first one, and is therefore a loop *of `B`* — of vanishing `ψ`-displacement
  since the winding span of `B` vanishes.  Its displacement, telescoping over the even parameters,
  is the displacement of `γ` itself.

So the winding vector of `γ` is the sum of the winding vectors of a loop of `A` and a loop of `B`,
each in the corresponding span, and the claim follows.  Note that the *path connectedness* of `B`
is in fact not used by this argument.

## Layout of the file

* `chainPath` — the concatenation of a finite chain of paths `c 0 → c 1 → ⋯ → c n`, with its
  `ψ`-displacement (`psiDisp_chainPath`) and its membership API (`chainPath_mem`);
* `psiDisp_id_eq_zero_of_span_eq_bot` — a loop lying in a region of vanishing winding span has
  vanishing displacement for the identity coefficient map;
* the main theorem.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.PinchLemma3.ClosedDiscA

noncomputable section

open scoped unitInterval

set_option linter.unusedVariables false

/-! ## 1. The concatenation of a chain of paths -/

/-- **The concatenation of a finite chain of paths.**  Given points `c i` of the carrier and paths
`u i : Path (c i) (c (i+1))` for `i < n`, this is the concatenated path from `c 0` to `c n`. -/
noncomputable def chainPath {P : Work.CoreTopology.ParamTorus} {c : ℕ → P.carrier} :
    ∀ (n : ℕ), (∀ i, i < n → Path (c i) (c (i+1))) → Path (c 0) (c n)
  | 0, _ => Path.refl (c 0)
  | n+1, u => (chainPath n (fun i hi => u i (Nat.lt_succ_of_lt hi))).trans
      (u n (Nat.lt_succ_self n))

/-- **The `ψ`-displacement of a chain is the sum of the displacements of its links.** -/
theorem psiDisp_chainPath {P : Work.CoreTopology.ParamTorus} {W : Type*} [AddCommGroup W]
    [Module ℝ W] (ψ : (ℝ × ℝ) →ₗ[ℝ] W) {c : ℕ → P.carrier} :
    ∀ (n : ℕ) (u : ∀ i, i < n → Path (c i) (c (i+1))),
    psiDisp ψ (chainPath n u) = ∑ i : Fin n, psiDisp ψ (u i.val i.isLt)
  | 0, u => by simp [chainPath, psiDisp_refl]
  | n+1, u => by
      rw [chainPath, psiDisp_trans, psiDisp_chainPath ψ n, Fin.sum_univ_castSucc]
      rfl

/-- **The image of a chain is contained in any set containing the images of its links.** -/
theorem chainPath_mem {P : Work.CoreTopology.ParamTorus} {c : ℕ → P.carrier} {X : Set R3}
    (hc0 : (c 0 : R3) ∈ X) :
    ∀ (n : ℕ) (u : ∀ i, i < n → Path (c i) (c (i+1))),
    (∀ i hi t, (u i hi t : R3) ∈ X) → ∀ t, ((chainPath n u) t : R3) ∈ X
  | 0, u, _, t => by simpa [chainPath, Path.refl_apply] using hc0
  | n+1, u, hu, t => by
      rw [chainPath, Path.trans_apply]
      by_cases ht : (t : ℝ) ≤ 1 / 2
      · rw [dif_pos ht]
        exact chainPath_mem hc0 n _ (fun i hi s => hu i (Nat.lt_succ_of_lt hi) s) _
      · rw [dif_neg ht]; exact hu n _ _

/-! ## 2. Loops in a region of vanishing winding span -/

/-- **A loop lying in a region of vanishing winding span has vanishing `ψ`-displacement.**  This is
`psiDisp_eq_zero_of_subset` with the coefficient map the identity and with `V = ⊥`: the only integer
vector of the zero span is `0`. -/
theorem psiDisp_id_eq_zero_of_span_eq_bot {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    (hVX : Work.SurgeryInvariance.WindingSpan P X = ⊥)
    {x : P.carrier} (u : Path x x) (hu : ∀ t : unitInterval, (u t : R3) ∈ X) :
    psiDisp (LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) u = 0 := by
  refine psiDisp_eq_zero_of_subset (V := ⊥) (X := X)
    (LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ?_ ?_ u hu
  · intro v hv
    rw [Submodule.mem_bot] at hv
    have h1 : (v.1 : ℚ) = 0 := congrArg Prod.fst hv
    have h2 : (v.2 : ℚ) = 0 := congrArg Prod.snd hv
    have h1' : ((v.1 : ℚ) : ℝ) = 0 := by exact_mod_cast h1
    have h2' : ((v.2 : ℚ) : ℝ) = 0 := by exact_mod_cast h2
    show (((v.1 : ℚ) : ℝ), ((v.2 : ℚ) : ℝ)) = 0
    rw [h1', h2']
    rfl
  · exact hVX ▸ le_rfl

/-! ## 3. The main theorem -/

theorem windingSpan_union_le_sup_of_grounded_inter {P : Work.CoreTopology.ParamTorus}
    {A B : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    (hA : Work.SurgeryInvariance.IsOpenInCarrier P A)
    (hB : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (hBconn : IsPathConnected B)
    (hground : ∀ x ∈ A ∩ B, ∀ y ∈ A ∩ B, JoinedIn A x y → JoinedIn (A ∩ B) x y)
    (hVA : Work.SurgeryInvariance.WindingSpan P A = ⊥)
    (hVB : Work.SurgeryInvariance.WindingSpan P B = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (A ∪ B) ≤
      Work.SurgeryInvariance.WindingSpan P A ⊔ Work.SurgeryInvariance.WindingSpan P B := by
  classical
  -- it suffices to show that every closed curve of `A ∪ B` has vanishing winding vector
  have key : ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ A ∪ B) →
      Work.SurgeryInvariance.windingOf P γ = 0 := by
    intro γ hγ
    rcases exists_alternating_partition hA hB γ hγ with
      hγA | hγB | ⟨k, hk, s, hs0, hslast, hmono, hArcA, hArcB⟩
    · -- the whole curve lies in `A`
      have hm : ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
          (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) ∈
          Work.SurgeryInvariance.WindingSpan P A := Submodule.subset_span ⟨γ, hγA, rfl⟩
      rw [hVA, Submodule.mem_bot] at hm
      exact (Work.SurgeryInvariance.intPair_cast_eq_zero_iff _).mp hm
    · -- the whole curve lies in `B`
      have hm : ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
          (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) ∈
          Work.SurgeryInvariance.WindingSpan P B := Submodule.subset_span ⟨γ, hγB, rfl⟩
      rw [hVB, Submodule.mem_bot] at hm
      exact (Work.SurgeryInvariance.intPair_cast_eq_zero_iff _).mp hm
    · -- the alternating decomposition
      obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
      set Λ : ℝ → ℝ × ℝ := fun t => (L.Θ t, L.Φ t) with hΛdef
      have hΛc : Continuous Λ := L.contΘ.prodMk L.contΦ
      have hΛmem : ∀ t : ℝ, Work.TorusCover.psiMap P.psi (Λ t) = γ t := by
        intro t; simp only [hΛdef, Work.TorusCover.psiMap]; exact L.lifts t
      let b : ℕ → P.carrier := fun i => ⟨γ (s i), γ.mem (s i)⟩
      have hs01 : s 0 ≤ s 1 := le_of_lt (hmono 0 1 (by omega) (by omega) (by omega))
      -- the block boundaries lie in `A` and in `B`
      have hA_even : ∀ j : ℕ, j ≤ k → γ (s (2 * j)) ∈ A := by
        intro j hj
        rcases lt_or_eq_of_le hj with hj' | hj'
        · exact hArcA j hj' (s (2 * j)) (le_refl _)
            (le_of_lt (hmono (2 * j) (2 * j + 1) (by omega) (by omega) (by omega)))
        · rw [hj', hslast, γ.periodic (s 0)]
          exact hArcA 0 hk (s 0) (le_refl _) hs01
      have hB_even : ∀ j : ℕ, j ≤ k → γ (s (2 * j)) ∈ B := by
        intro j hj
        rcases Nat.eq_zero_or_pos j with hj' | hj'
        · rw [hj', ← γ.periodic (s 0), ← hslast]
          exact hArcB (k - 1) (by omega) (s (2 * k))
            (le_of_lt (hmono (2 * (k - 1) + 1) (2 * k) (by omega) (by omega) (by omega)))
            (le_of_eq (by congr 1; omega))
        · exact hArcB (j - 1) (by omega) (s (2 * j))
            (le_of_lt (hmono (2 * (j - 1) + 1) (2 * j) (by omega) (by omega) (by omega)))
            (le_of_eq (by congr 1; omega))
      have hA_odd : ∀ j : ℕ, j < k → γ (s (2 * j + 1)) ∈ A := fun j hj =>
        hArcA j hj (s (2 * j + 1))
          (le_of_lt (hmono (2 * j) (2 * j + 1) (by omega) (by omega) (by omega))) (le_refl _)
      have hB_odd : ∀ j : ℕ, j < k → γ (s (2 * j + 1)) ∈ B := fun j hj =>
        hArcB j hj (s (2 * j + 1)) (le_refl _)
          (le_of_lt (hmono (2 * j + 1) (2 * j + 2) (by omega) (by omega) (by omega)))
      have hbd : ∀ i : ℕ, i ≤ 2 * k → γ (s i) ∈ A ∩ B := by
        intro i hi
        rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
        · subst hj
          rw [show j + j = 2 * j from by omega]
          exact ⟨hA_even j (by omega), hB_even j (by omega)⟩
        · subst hj
          exact ⟨hA_odd j (by omega), hB_odd j (by omega)⟩
      -- the `A`-arcs
      let a : (j : Fin k) → Path (b (2 * j.val)) (b (2 * j.val + 1)) :=
        fun j => subArc γ (s (2 * j.val)) (s (2 * j.val + 1))
      have ha_mem : ∀ (j : Fin k) (t : unitInterval), ((a j) t : R3) ∈ A := by
        intro j t
        exact subArc_coe_mem γ
          (le_of_lt (hmono (2 * j.val) (2 * j.val + 1) (by have := j.isLt; omega)
            (by have := j.isLt; omega) (by have := j.isLt; omega)))
          (fun u hu1 hu2 => hArcA j.val j.isLt u hu1 hu2) t
      -- the grounded connectors inside `A ∩ B`
      have hconn : ∀ j : Fin k, ∃ c : Path (b (2 * j.val)) (b (2 * j.val + 1)),
          ∀ t : unitInterval, (c t : R3) ∈ A ∩ B := by
        intro j
        have hj := j.isLt
        have hx : (b (2 * j.val) : R3) ∈ A ∩ B := hbd (2 * j.val) (by omega)
        have hy : (b (2 * j.val + 1) : R3) ∈ A ∩ B := hbd (2 * j.val + 1) (by omega)
        obtain ⟨c, hc⟩ := hground (b (2 * j.val)) hx (b (2 * j.val + 1)) hy
          ⟨(a j).map continuous_subtype_val, fun t => by
            show (((a j).map continuous_subtype_val) t) ∈ A
            rw [Path.map_coe]
            exact ha_mem j t⟩
        refine ⟨⟨⟨fun t => ⟨c t, hAc (hc t).1⟩, c.continuous.subtype_mk _⟩, ?_, ?_⟩,
          fun t => ⟨(hc t).1, (hc t).2⟩⟩
        · exact Subtype.ext c.source
        · exact Subtype.ext c.target
      let e : (j : Fin k) → Path (b (2 * j.val)) (b (2 * j.val + 1)) :=
        fun j => Classical.choose (hconn j)
      have he : ∀ (j : Fin k) (t : unitInterval), (e j t : R3) ∈ A ∩ B :=
        fun j => Classical.choose_spec (hconn j)
      let ψid : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := LinearMap.id
      -- each `A`-arc closes up through `A ∩ B` into a loop of `A`, which has vanishing displacement
      have hAloop : ∀ j : Fin k, psiDisp ψid ((a j).trans ((e j).symm)) = 0 := by
        intro j
        exact psiDisp_id_eq_zero_of_span_eq_bot hVA ((a j).trans ((e j).symm)) (fun t =>
          Path.trans_coe_mem (a j) ((e j).symm) (fun u => ha_mem j u)
            (Path.symm_coe_mem (e j) (fun u => (he j u).1)) t)
      have hDa : ∀ j : Fin k, psiDisp ψid (a j) = psiDisp ψid (e j) := by
        intro j
        have h := hAloop j
        rw [psiDisp_trans, psiDisp_symm] at h
        have h'' : psiDisp ψid (a j) - psiDisp ψid (e j) = 0 := by
          simpa [sub_eq_add_neg] using h
        exact sub_eq_zero.mp h''
      -- the chain of `B`-pieces: `e_j` followed by the `B`-arc from `s (2j+1)` to `s (2j+2)`
      let bb : ∀ j, j < k → Path (b (2 * j + 1)) (b (2 * j + 2)) := fun j _ =>
        subArc γ (s (2 * j + 1)) (s (2 * j + 2))
      have hbb_mem : ∀ (j : ℕ) (hj : j < k) (t : unitInterval), ((bb j hj) t : R3) ∈ B := by
        intro j hj t
        exact subArc_coe_mem γ
          (le_of_lt (hmono (2 * j + 1) (2 * j + 2) (by omega) (by omega) (by omega)))
          (fun u hu1 hu2 => hArcB j hj u hu1 hu2) t
      let c : ℕ → P.carrier := fun j => b (2 * j)
      let w : ∀ j, j < k → Path (c j) (c (j + 1)) := fun j hj => (e ⟨j, hj⟩).trans (bb j hj)
      have hw_mem : ∀ j (hj : j < k) (t : unitInterval), ((w j hj) t : R3) ∈ B := by
        intro j hj t
        exact Path.trans_coe_mem (Y := B) (e ⟨j, hj⟩) (bb j hj) (fun u => (he ⟨j, hj⟩ u).2)
          (fun u => hbb_mem j hj u) t
      have hck : c k = b 0 := Subtype.ext (by
        show γ (s (2 * k)) = γ (s 0)
        rw [hslast]; exact γ.periodic (s 0))
      have hchain_mem : ∀ t : unitInterval, ((chainPath k w) t : R3) ∈ B := by
        refine chainPath_mem (X := B) ?_ k w hw_mem
        exact hB_even 0 (by omega)
      -- the chain closes up into a loop of `B`, which has vanishing displacement
      have hchain_psi : psiDisp ψid (chainPath k w) = 0 := by
        let loop : Path (b 0) (b 0) :=
          ⟨(chainPath k w).toContinuousMap, (chainPath k w).source,
            (chainPath k w).target.trans hck⟩
        have hloop_mem : ∀ t : unitInterval, (loop t : R3) ∈ B := fun t => hchain_mem t
        have h0 : psiDisp ψid loop = 0 := psiDisp_id_eq_zero_of_span_eq_bot hVB loop hloop_mem
        exact (show psiDisp ψid loop = psiDisp ψid (chainPath k w) from rfl) ▸ h0
      have hsum : ∑ j : Fin k, psiDisp ψid (w j.val j.isLt) = 0 := by
        rw [← psiDisp_chainPath ψid k w]
        exact hchain_psi
      -- the displacement of the `j`-th link
      have hsummand : ∀ j : Fin k, psiDisp ψid (w j.val j.isLt) =
          Λ (s (2 * j.val + 2)) - Λ (s (2 * j.val)) := by
        intro j
        have hj := j.isLt
        show psiDisp ψid ((e ⟨j.val, hj⟩).trans (bb j.val hj)) =
          Λ (s (2 * j.val + 2)) - Λ (s (2 * j.val))
        rw [psiDisp_trans, ← hDa ⟨j.val, hj⟩,
          psiDisp_subArc ψid γ (s (2 * j.val)) (s (2 * j.val + 1)) Λ hΛc hΛmem,
          psiDisp_subArc ψid γ (s (2 * j.val + 1)) (s (2 * j.val + 2)) Λ hΛc hΛmem]
        simp [ψid]
      -- telescoping over the even parameters
      have htel : ∑ j : Fin k, (Λ (s (2 * j.val + 2)) - Λ (s (2 * j.val))) =
          Λ (s (2 * k)) - Λ (s 0) := by
        have hsum1 : (∑ j : Fin k, (Λ (s (2 * j.val + 2)) - Λ (s (2 * j.val))))
            = ∑ j ∈ Finset.range k, (Λ (s (2 * (j + 1))) - Λ (s (2 * j))) := by
          rw [Fin.sum_univ_eq_sum_range (fun j => Λ (s (2 * j + 2)) - Λ (s (2 * j))) k]
          exact Finset.sum_congr rfl (fun j _ => by rw [Nat.mul_succ])
        rw [hsum1, Finset.sum_range_sub (fun j => Λ (s (2 * j)))]
      have hzero : Λ (s (2 * k)) - Λ (s 0) = 0 := by
        rw [← htel]
        exact (Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hsummand j)).symm.trans hsum
      have hΛeq : Λ (s (2 * k)) = Λ (s 0) := sub_eq_zero.mp hzero
      have hper : Λ (s (2 * k)) =
          Λ (s 0) + Work.TorusCover.periodShift (Work.SurgeryInvariance.windingOf P γ) := by
        have h := L.period_shift_winding (s 0)
        have hw := Work.SurgeryInvariance.windingOf_eq P γ L
        rw [hslast, hw]
        ext <;> simp [hΛdef, Work.TorusCover.periodShift, h.1, h.2]
      have hps : Work.TorusCover.periodShift (Work.SurgeryInvariance.windingOf P γ) = 0 := by
        have h2 : Λ (s 0) + Work.TorusCover.periodShift (Work.SurgeryInvariance.windingOf P γ)
            = Λ (s 0) := by
          rw [← hper]; exact hΛeq
        have h3 : Λ (s 0) + Work.TorusCover.periodShift (Work.SurgeryInvariance.windingOf P γ)
            = Λ (s 0) + 0 := by simpa using h2
        exact add_left_cancel h3
      have h1 : (Work.SurgeryInvariance.windingOf P γ).1 = 0 := by
        have hf := congrArg Prod.fst hps
        simp only [Work.TorusCover.periodShift, Prod.fst_zero] at hf
        rcases mul_eq_zero.mp hf with h | h
        · exact_mod_cast h
        · exact absurd h (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi))
      have h2 : (Work.SurgeryInvariance.windingOf P γ).2 = 0 := by
        have hf := congrArg Prod.snd hps
        simp only [Work.TorusCover.periodShift, Prod.snd_zero] at hf
        rcases mul_eq_zero.mp hf with h | h
        · exact_mod_cast h
        · exact absurd h (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi))
      exact Prod.ext h1 h2
  rw [hVA, hVB, sup_bot_eq, le_bot_iff, Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, hess, hγ⟩
  exact (Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ).mp hess (key γ hγ)

end

end Work.PinchLemma3.ClosedDiscA
