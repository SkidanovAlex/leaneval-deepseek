import Mathlib
import Submission.Work.WilE2.VcbDefs
import Submission.Work.WilE2.mv_locallyConnected
import Submission.Work.WilE2.locallyConnected_cubeC_Zset

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E

noncomputable section

/-!
  ## `posVariety_pdist_bound`

  The number of points of `X = cubeC k ∩ {f = 0} ∩ {G > 0}` carrying pairwise distinct connected
  components is bounded polynomially in the degree datum `∑ h ∈ f, atomDeg h + atomDeg G`, given
  the variety bound `VarietyBound F`.

  The argument is the classical reduction of Gabrielov–Vorobjov Theorem 3.4 (Zell's "basic set
  bound"):

  * choose the level `c₀ = (1/2) min_{x ∈ s} G(x) > 0`; then `s ⊆ R := cubeC ∩ {f = 0} ∩ {G ≥ c₀}`
    and `R ⊆ X`, so distinct `X`-components of points of `s` are distinct `R`-components;
  * the superlevel `R` of the *continuous* function `G` on the variety `V = cubeC ∩ {f = 0}`
    satisfies `#components R ≤ #components V + #components L` where `L = V ∩ {G = c₀}` (a
    Mayer–Vietoris-type inequality for the pair `({G ≥ c₀}, {G ≤ c₀})`,
    `mv_superlevel_encard`);
  * `#components V` and `#components L` are bounded by the sizes of the hitting sets that
    `VarietyBound F` provides for the families `f` and `f ∪ {G - c₀}`.
-/

/-! ## §1. Elementary evaluation and degree lemmas -/

/-- `eaEval` of a constant shift. -/
private lemma eaEval_sub_const {k r : ℕ} (c : EAChain k r) (P : EAPoly k r) (a : ℝ)
    (x : Fin k → ℝ) : eaEval c (P - MvPolynomial.C a) x = eaEval c P x - a := by
  simp only [eaEval, map_sub, MvPolynomial.eval_C]

/-- Subtracting a constant does not increase the atom degree. -/
private lemma atomDeg_sub_C_le {k r : ℕ} (P : EAPoly k r) (a : ℝ) :
    atomDeg (P - MvPolynomial.C a) ≤ atomDeg P := by
  have h : (P - MvPolynomial.C a).totalDegree ≤ P.totalDegree := by
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [MvPolynomial.totalDegree_C]
    exact max_le le_rfl (Nat.zero_le _)
  exact Nat.add_le_add_right h 1

/-- Sum of `atomDeg` over `f ∪ {P}` is at most the sum over `f` plus `atomDeg P`. -/
private lemma sum_atomDeg_union_singleton_le {k r : ℕ} (f : Finset (EAPoly k r)) (P : EAPoly k r) :
    (∑ h ∈ f ∪ {P}, atomDeg h) ≤ (∑ h ∈ f, atomDeg h) + atomDeg P := by
  rw [Finset.union_singleton]
  by_cases hP : P ∈ f
  · rw [Finset.insert_eq_of_mem hP]
    exact Nat.le_add_right _ _
  · rw [Finset.sum_insert hP]
    exact le_of_eq (add_comm _ _)

/-- `eaEval` is continuous. -/
private lemma continuous_eaEval {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) :
    Continuous (fun x : Fin k → ℝ => eaEval c Q x) := by
  show Continuous (fun x => MvPolynomial.eval (Sum.elim x fun j => Real.exp (c.ell j x)) Q)
  refine (MvPolynomial.continuous_eval Q).comp ?_
  refine continuous_pi (fun v => ?_)
  rcases v with i | j
  · exact continuous_apply i
  · refine Real.continuous_exp.comp ?_
    have h : c.ell j = fun x : Fin k → ℝ => ∑ i, c.a j i * x i + c.b j := by
      funext x; simp only [EAChain.ell]
    rw [h]
    exact (continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))).add
      continuous_const

/-- Monotonicity of polynomial evaluation on the naturals. -/
private lemma eval_mono_nat_pv (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h k)

/-- The `Zset` of `f ∪ {P - C a}` is the intersection of `Zset c f` with the level set `{P = a}`. -/
private lemma Zset_union_singleton_sub_C {k r : ℕ} (c : EAChain k r)
    (f : Finset (EAPoly k r)) (P : EAPoly k r) (a : ℝ) :
    Zset c (f ∪ {P - MvPolynomial.C a}) = Zset c f ∩ {x | eaEval c P x = a} := by
  ext x
  simp only [Zset, Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro h
    refine ⟨fun Q hQ => h Q (Or.inl hQ), ?_⟩
    have h' := h (P - MvPolynomial.C a) (Or.inr rfl)
    rw [eaEval_sub_const, sub_eq_zero] at h'
    exact h'
  · rintro ⟨h1, h2⟩ Q (hQ | hQ)
    · exact h1 Q hQ
    · rw [hQ, eaEval_sub_const, h2, sub_self]

/-! ## §2. Component counting via hitting sets -/

/-- The component set of `A` is contained in the components of the hitting points together with
the empty set (the component of a point outside `A`). -/
private lemma range_component_subset {α : Type*} [TopologicalSpace α] {A : Set α} {t : Finset α}
    (ht : ∀ x ∈ A, ∃ y ∈ t, connectedComponentIn A x = connectedComponentIn A y) :
    Set.range (connectedComponentIn A) ⊆
      (t.image (fun y => connectedComponentIn A y) : Set (Set α)) ∪ {(∅ : Set α)} := by
  rintro C ⟨x, rfl⟩
  by_cases hx : x ∈ A
  · obtain ⟨y, hy, hyc⟩ := ht x hx
    exact Or.inl (Finset.mem_image.mpr ⟨y, hy, hyc.symm⟩)
  · rw [connectedComponentIn_eq_empty hx]
    exact Or.inr rfl

/-- The number of components of a set hit by a finite set `t` is at most `t.card + 1`. -/
private lemma encard_range_component_le_hitting {α : Type*} [TopologicalSpace α] {A : Set α}
    {t : Finset α}
    (ht : ∀ x ∈ A, ∃ y ∈ t, connectedComponentIn A x = connectedComponentIn A y) :
    (Set.range (connectedComponentIn A)).encard ≤ ((t.card + 1 : ℕ) : ℕ∞) := by
  have hsub := range_component_subset ht
  have h1 : (t.image (fun y => connectedComponentIn A y) : Set (Set α)).encard
      ≤ ((t.card : ℕ) : ℕ∞) := by
    have h := Set.encard_image_le (fun y => connectedComponentIn A y) (↑t : Set α)
    rw [Set.encard_coe_eq_coe_finsetCard] at h
    rwa [Finset.coe_image]
  calc (Set.range (connectedComponentIn A)).encard
      ≤ ((t.image (fun y => connectedComponentIn A y) : Set (Set α)) ∪
          {(∅ : Set α)}).encard := Set.encard_le_encard hsub
    _ ≤ (t.image (fun y => connectedComponentIn A y) : Set (Set α)).encard +
          ({∅} : Set (Set α)).encard := Set.encard_union_le _ _
    _ = (t.image (fun y => connectedComponentIn A y) : Set (Set α)).encard + 1 := by
          rw [Set.encard_singleton]
    _ ≤ ((t.card : ℕ) : ℕ∞) + 1 := by gcongr
    _ = ((t.card + 1 : ℕ) : ℕ∞) := by push_cast; ring

/-- A finite set of points of `A` with pairwise distinct `A`-components has cardinality at most the
number of components of `A`. -/
private lemma card_le_encard_range_component {α : Type*} [TopologicalSpace α] {A : Set α}
    (s : Finset α)
    (hpd : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → connectedComponentIn A x ≠ connectedComponentIn A y) :
    ((s.card : ℕ) : ℕ∞) ≤ (Set.range (connectedComponentIn A)).encard := by
  have hinj : Set.InjOn (fun x => connectedComponentIn A x) (↑s : Set α) := by
    intro x hx y hy hxy
    by_contra hne
    exact hpd x hx y hy hne hxy
  have hcard : (s.image (fun x => connectedComponentIn A x)).card = s.card :=
    Finset.card_image_of_injOn hinj
  have hsub : ((s.image (fun x => connectedComponentIn A x) : Finset (Set α)) : Set (Set α)) ⊆
      Set.range (connectedComponentIn A) := by
    intro C hC
    rw [Finset.mem_coe, Finset.mem_image] at hC
    obtain ⟨x, -, rfl⟩ := hC
    exact ⟨x, rfl⟩
  calc ((s.card : ℕ) : ℕ∞)
      = ((s.image (fun x => connectedComponentIn A x) : Finset (Set α)) : Set (Set α)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, hcard]
    _ ≤ (Set.range (connectedComponentIn A)).encard := Set.encard_le_encard hsub

/-! ## §3. The target -/

theorem posVariety_pdist_bound (F : ℕ) (hvar : Work.WilE2.VarietyBound F) :
    ∃ p : Polynomial ℕ,
      ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r) (f : Finset (WilkiesDesign.E.EAPoly k r))
        (G : WilkiesDesign.E.EAPoly k r), k + r ≤ F →
      ∀ s : Finset (Fin k → ℝ),
        (∀ x ∈ s, x ∈ WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset c f ∩
          {x | 0 < WilkiesDesign.E.eaEval c G x}) →
        (∀ x ∈ s, ∀ y ∈ s, x ≠ y →
          connectedComponentIn (WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset c f ∩
            {x | 0 < WilkiesDesign.E.eaEval c G x}) x ≠
          connectedComponentIn (WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset c f ∩
            {x | 0 < WilkiesDesign.E.eaEval c G x}) y) →
        s.card ≤ p.eval (∑ h ∈ f, WilkiesDesign.E.atomDeg h + WilkiesDesign.E.atomDeg G) := by
  obtain ⟨p_v, hp_v⟩ := hvar
  refine ⟨2 * p_v + 2, ?_⟩
  intro k r c f G hkr s hs hpd
  by_cases hsne : s.Nonempty
  · -- the level `c₀ = (1/2) * min_{x ∈ s} G(x) > 0`
    set m : ℝ := (s.image (fun x => eaEval c G x)).min' (hsne.image _) with hm
    set c₀ : ℝ := (1/2) * m with hc₀
    have hm_pos : 0 < m := by
      rw [hm, Finset.lt_min'_iff]
      intro a ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      exact (hs x hx).2
    have hc₀_pos : 0 < c₀ := by rw [hc₀]; positivity
    have hc₀_le : ∀ x ∈ s, c₀ ≤ eaEval c G x := by
      intro x hx
      have h1 : m ≤ eaEval c G x := by
        rw [hm]; exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      have h2 : (0:ℝ) < eaEval c G x := (hs x hx).2
      rw [hc₀]; linarith
    -- `s ⊆ R` and distinct `R`-components (with `R = cubeC ∩ Zset c f ∩ {G ≥ c₀}`)
    have hsR : (↑s : Set (Fin k → ℝ)) ⊆
        WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | c₀ ≤ eaEval c G x} := by
      intro x hx
      exact ⟨(hs x hx).1, hc₀_le x hx⟩
    have hXR : WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | c₀ ≤ eaEval c G x} ⊆
        WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | 0 < eaEval c G x} := by
      rintro z ⟨hz, hzc⟩
      exact ⟨hz, lt_of_lt_of_le hc₀_pos hzc⟩
    have hRcomp : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        connectedComponentIn (WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | c₀ ≤ eaEval c G x}) x ≠
        connectedComponentIn (WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | c₀ ≤ eaEval c G x}) y := by
      intro x hx y hy hne hcon
      have hxR : x ∈ WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | c₀ ≤ eaEval c G x} := hsR hx
      have hxXy : x ∈ connectedComponentIn
          (WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | 0 < eaEval c G x}) y :=
        (connectedComponentIn_mono y hXR) (hcon ▸ mem_connectedComponentIn hxR)
      exact (hpd x hx y hy hne) (connectedComponentIn_eq hxXy).symm
    -- the hitting sets provided by `VarietyBound`
    obtain ⟨tV, htV1, htV2, htV3⟩ := hp_v k r c f hkr
    have htV3' : ∀ x ∈ WilkiesDesign.E.cubeC k ∩ Zset c f, ∃ y ∈ tV,
        connectedComponentIn (WilkiesDesign.E.cubeC k ∩ Zset c f) x =
          connectedComponentIn (WilkiesDesign.E.cubeC k ∩ Zset c f) y := htV3
    obtain ⟨tL, htL_1, htL_2, htL_3⟩ := hp_v k r c (f ∪ {G - MvPolynomial.C c₀}) hkr
    have hset : (WilkiesDesign.E.cubeC k ∩ Zset c (f ∪ {G - MvPolynomial.C c₀})) =
        WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | eaEval c G x = c₀} := by
      rw [Zset_union_singleton_sub_C, ← Set.inter_assoc]
    have htL3' : ∀ x ∈ WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | eaEval c G x = c₀},
        ∃ y ∈ tL, connectedComponentIn
            (WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | eaEval c G x = c₀}) x =
          connectedComponentIn
            (WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | eaEval c G x = c₀}) y := by
      intro x hx
      obtain ⟨⟨hxC, hxZ⟩, hxG⟩ := hx
      have hxBig : x ∈ WilkiesDesign.E.cubeC k ∩
          Zset c (f ∪ {G - MvPolynomial.C c₀}) := by
        rw [hset]; exact ⟨⟨hxC, hxZ⟩, hxG⟩
      obtain ⟨y, hy, hyc⟩ := htL_3 x hxBig
      exact ⟨y, hy, hset ▸ hyc⟩
    -- the Mayer–Vietoris inequality
    have hcont : ContinuousOn (fun x : Fin k → ℝ => eaEval c G x)
        (WilkiesDesign.E.cubeC k ∩ Zset c f) := (continuous_eaEval c G).continuousOn
    haveI : LocallyConnectedSpace ↥(WilkiesDesign.E.cubeC k ∩ Zset c f) :=
      locallyConnected_cubeC_Zset k r c f
    have hmv := mv_locallyConnected (WilkiesDesign.E.cubeC k ∩ Zset c f)
      (fun x : Fin k → ℝ => eaEval c G x) c₀ hcont
    -- bounds on the two component counts
    have hLle : (Set.range (connectedComponentIn
        (WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | eaEval c G x = c₀}))).encard
        ≤ ((tL.card + 1 : ℕ) : ℕ∞) := encard_range_component_le_hitting htL3'
    have hVle : (Set.range (connectedComponentIn
        (WilkiesDesign.E.cubeC k ∩ Zset c f))).encard ≤ ((tV.card + 1 : ℕ) : ℕ∞) :=
      encard_range_component_le_hitting htV3'
    have hmvsum : (Set.range (connectedComponentIn
        (WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | c₀ ≤ eaEval c G x}))).encard ≤
        ((tL.card + 1 + (tV.card + 1) : ℕ) : ℕ∞) := by
      calc (Set.range (connectedComponentIn
              (WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | c₀ ≤ eaEval c G x}))).encard
          ≤ (Set.range (connectedComponentIn
              (WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | eaEval c G x = c₀}))).encard +
            (Set.range (connectedComponentIn
              (WilkiesDesign.E.cubeC k ∩ Zset c f))).encard := hmv
        _ ≤ ((tL.card + 1 : ℕ) : ℕ∞) + ((tV.card + 1 : ℕ) : ℕ∞) := add_le_add hLle hVle
        _ = ((tL.card + 1 + (tV.card + 1) : ℕ) : ℕ∞) := by push_cast; ring
    have htL_le : tL.card ≤ p_v.eval ((∑ h ∈ f, atomDeg h) + atomDeg G) := by
      refine le_trans htL_1 (eval_mono_nat_pv p_v ?_)
      exact le_trans (sum_atomDeg_union_singleton_le f (G - MvPolynomial.C c₀))
        (Nat.add_le_add_left (atomDeg_sub_C_le G c₀) _)
    have htV_le : tV.card ≤ p_v.eval ((∑ h ∈ f, atomDeg h) + atomDeg G) := by
      refine le_trans htV1 (eval_mono_nat_pv p_v ?_)
      exact Nat.le_add_right _ _
    -- the bound on the number of components of `R`
    have hRbound : (Set.range (connectedComponentIn
        (WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | c₀ ≤ eaEval c G x}))).encard ≤
        ((2 * p_v.eval ((∑ h ∈ f, atomDeg h) + atomDeg G) + 2 : ℕ) : ℕ∞) := by
      refine le_trans hmvsum ?_
      norm_cast
      omega
    have hs_card : ((s.card : ℕ) : ℕ∞) ≤ (Set.range (connectedComponentIn
        (WilkiesDesign.E.cubeC k ∩ Zset c f ∩ {x | c₀ ≤ eaEval c G x}))).encard :=
      card_le_encard_range_component s hRcomp
    have hsN : s.card ≤ 2 * p_v.eval ((∑ h ∈ f, atomDeg h) + atomDeg G) + 2 := by
      have := le_trans hs_card hRbound
      exact_mod_cast this
    -- conclude
    have heval : (2 * p_v + 2).eval ((∑ h ∈ f, atomDeg h) + atomDeg G) =
        2 * p_v.eval ((∑ h ∈ f, atomDeg h) + atomDeg G) + 2 := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    rw [heval]
    exact hsN
  · rw [Finset.not_nonempty_iff_eq_empty] at hsne
    rw [hsne, Finset.card_empty]
    exact Nat.zero_le _

end

end Work.WilE2
