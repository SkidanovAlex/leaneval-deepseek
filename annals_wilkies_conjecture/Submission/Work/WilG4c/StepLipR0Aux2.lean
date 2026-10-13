/-
  WilG4c / StepLipR0, auxiliary module: the projection lemma, the per-cell chart and the
  polynomial bookkeeping used by `StepLipR0`.
-/
import Mathlib
import Submission.Work.WilG4c.StepLipR0Aux1
import Submission.Work.WilG4c.CellTowerCont
import Submission.Work.WilG1.Cell.thin_union
import Submission.Work.WilG5.PolyEval.nat_poly_bound

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c
open Work.WilG1

/-! ## 0. Helpers -/

/-- `famFun` of a glued vector. -/
theorem famFun_append'_aux {p M : ℕ} (f : (Fin p → ℝ) → (Fin M → ℝ) → ℝ) (l : Fin p → ℝ)
    (u : Fin M → ℝ) : famFun f (Fin.append l u) = f l u := by
  rw [famFun]
  congr 1
  · funext i; exact Fin.append_left l u i
  · funext j; exact Fin.append_right l u j

/-- The nested `Fin.snoc` vector of `WilG0` is `Fin.append`. -/
theorem snocIt_eq_append' (n m : ℕ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    Work.WilG0.snocIt n m x w = Fin.append x w := by
  funext i
  cases i using Fin.addCases with
  | left i' => rw [Work.WilG0.snocIt_castAdd, Fin.append_left]
  | right j => rw [Work.WilG0.snocIt_natAdd, Fin.append_right]

/-- A cell lying in the lift of `A` projects into `A`; a cell disjoint from the lift projects
to a set disjoint from `A`. -/
theorem image_init_subset_or_disjoint {p N : ℕ} {c : Set (Fin (p + N + 1) → ℝ)}
    {A : Set (Fin (p + N) → ℝ)}
    (h : c ⊆ {z | Fin.init z ∈ A} ∨ Disjoint c {z | Fin.init z ∈ A}) :
    Fin.init '' c ⊆ A ∨ Disjoint (Fin.init '' c) A := by
  rcases h with h | h
  · left
    rintro q ⟨z, hz, rfl⟩
    exact h hz
  · right
    rw [Set.disjoint_left] at h ⊢
    rintro q ⟨z, hz, hzq⟩ hqA
    exact h hz (by change Fin.init z ∈ A; rw [hzq]; exact hqA)

/-- `ChartsOK` is monotone in the format and the degree. -/
theorem ChartsOK.mono {S : SOMin} {p n k a a' Dg Dg' r : ℕ} {Λ : Set (Fin p → ℝ)}
    {F : Family k p n} {Φ : Finset (ChartTuple p n)} (h : ChartsOK S a Dg r Λ F Φ)
    (ha : a ≤ a') (hD : Dg ≤ Dg') : ChartsOK S a' Dg' r Λ F Φ :=
  fun φ hφ => ⟨fun j => Omega_mono_le S ha hD ((h φ hφ).1 j), (h φ hφ).2⟩

/-- `ChartsOK` over a `Finset.biUnion`. -/
theorem ChartsOK.biUnion {S : SOMin} {p n k a Dg r : ℕ} {Λ : Set (Fin p → ℝ)}
    {F : Family k p n} {ι : Type*} {C : Finset ι}
    {f : ι → Finset (ChartTuple p n)} (h : ∀ i ∈ C, ChartsOK S a Dg r Λ F (f i)) :
    ChartsOK S a Dg r Λ F (C.biUnion f) := fun φ hφ => by
  obtain ⟨i, hi, hφi⟩ := Finset.mem_biUnion.mp hφ
  exact h i hi φ hφi

/-- The lift of `inCubeSet` to one more dimension is `Ω`-bounded. -/
theorem lift_inCubeSet_mem' (S : SOMin) (p N : ℕ) :
    {z : Fin (p + N + 1) → ℝ | Fin.init z ∈ inCubeSet p N} ∈
      S.Ω (p + N + 4 + 1) (6 * N) (p + N + 1) :=
  S.prod_right (inCubeSet_mem S p N)

/-- A shifted count bound for a two-variable `ℕ`-polynomial, in `Fin 4` form. -/
theorem polyCountEval_shift (b : MvPolynomial (Fin 2) ℕ) (K : ℕ) :
    ∃ c : MvPolynomial (Fin 4) ℝ, ∀ (D k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ((MvPolynomial.eval ![D + K, k + 1] b : ℕ) : ℝ) ≤
        MvPolynomial.eval ![(D : ℝ), (0 : ℝ), (k : ℝ), -Real.log ε] c := by
  obtain ⟨A, N, hA, hbound⟩ := Work.WilG5.PolyEval.nat_poly_bound b
  refine ⟨MvPolynomial.C A * (MvPolynomial.X (0 : Fin 4) + MvPolynomial.X (2 : Fin 4)
      + MvPolynomial.C ((K : ℝ) + 2)) ^ N, ?_⟩
  intro D k ε hε hε1
  have hb := hbound ![D + K, k + 1]
  have hsum : (∑ i : Fin 2, (((![D + K, k + 1] : Fin 2 → ℕ) i : ℕ) : ℝ))
      = (D : ℝ) + (k : ℝ) + ((K : ℝ) + 1) := by
    simp [Fin.sum_univ_two]
    push_cast
    ring
  rw [hsum] at hb
  have hbase : (1 : ℝ) + ((D : ℝ) + (k : ℝ) + ((K : ℝ) + 1))
      = (D : ℝ) + (k : ℝ) + ((K : ℝ) + 2) := by ring
  rw [hbase] at hb
  have heval : MvPolynomial.eval ![(D : ℝ), (0 : ℝ), (k : ℝ), -Real.log ε]
      (MvPolynomial.C A * (MvPolynomial.X (0 : Fin 4) + MvPolynomial.X (2 : Fin 4)
        + MvPolynomial.C ((K : ℝ) + 2)) ^ N)
      = A * ((D : ℝ) + (k : ℝ) + ((K : ℝ) + 2)) ^ N := by
    simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, MvPolynomial.eval_C]
  rw [heval]
  exact hb

/-- **The projected decomposition of a decomposition compatible with a graph.** -/
theorem continuousOn_of_mem_projDecomp' {p N : ℕ} {f : (Fin (p + N) → ℝ) → ℝ}
    {D : Finset (Set (Fin (p + N + 1) → ℝ))}
    (hD : IsCylDecomp (p + N + 1) D)
    (hcomp : ∀ c ∈ D, c ⊆ graphOf f ∨ Disjoint c (graphOf f)) :
    ∀ κ ∈ D.image (fun c => Fin.init '' c), ContinuousOn f κ := by
  intro κ hκ
  obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hκ
  obtain ⟨hcellD, -, hcoverD, hprojD⟩ := (IsCylDecomp.eq_2 (p + N) D).mp hD
  have hpdisj : ((D.image (fun c => Fin.init '' c)) : Set (Set (Fin (p + N) → ℝ))).PairwiseDisjoint
      id := Work.WilG1.Cell.pairwiseDisjoint_of_cylDecomp hprojD
  rw [Set.PairwiseDisjoint, Set.Pairwise] at hpdisj
  by_cases hemp : (Fin.init '' c₀ : Set (Fin (p + N) → ℝ)) = ∅
  · rw [hemp]; exact continuousOn_empty f
  · obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.mpr hemp
    have hpt : Fin.snoc q (f q) ∈ graphOf f := by
      rw [graphOf, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
    obtain ⟨c, hc, hzc⟩ := hcoverD (Fin.snoc q (f q))
    have hcgraph : c ⊆ graphOf f := by
      rcases hcomp c hc with h | h
      · exact h
      · exact (Set.disjoint_left.mp h hzc hpt).elim
    have hcq : q ∈ Fin.init '' c := ⟨Fin.snoc q (f q), hzc, by simp⟩
    have hceq : Fin.init '' c = Fin.init '' c₀ := by
      by_contra hne
      exact (Set.disjoint_left.mp (hpdisj (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
        (Finset.mem_image.mpr ⟨c₀, hc₀, rfl⟩) hne) hcq hq).elim
    have hcellc : IsCell (p + N + 1) c := (hcellD c hc).1
    rcases Work.WilG1.Cell.cell_cases hcellc with ⟨τ, g, hg, hτ⟩ | ⟨τ, a, b, ha, hb, hab, hτ⟩
    · -- graph case: `c` is the graph of `g` over `τ`, and `f = g` on `τ`
      have hprojc : Fin.init '' c = τ := by
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ((hτ z).mp hz).1
        · intro hx
          exact ⟨Fin.snoc x (g x), (hτ _).mpr ⟨by simpa using hx, by simp⟩, by simp⟩
      have hτκ : τ = Fin.init '' c₀ := by rw [← hprojc]; exact hceq
      have hgf : ∀ x ∈ τ, g x = f x := by
        intro x hx
        have hmem : Fin.snoc x (g x) ∈ graphOf f := hcgraph ((hτ _).mpr ⟨by simpa using hx, by simp⟩)
        rw [graphOf, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hmem
        exact hmem
      rw [← hτκ]
      exact hg.congr fun x hx => (hgf x hx).symm
    · -- band case: a band cell cannot be contained in the graph of a function
      obtain ⟨z, hz⟩ := (hcellD c hc).2
      have hz1 : Fin.init z ∈ τ := ((hτ z).mp hz).1
      have hz2 : a (Fin.init z) < ((z (Fin.last (p + N)) : ℝ) : EReal) := ((hτ z).mp hz).2.1
      have hz3 : ((z (Fin.last (p + N)) : ℝ) : EReal) < b (Fin.init z) := ((hτ z).mp hz).2.2
      have hz' := hcgraph hz
      rw [graphOf, Set.mem_ofPred_eq] at hz'
      obtain ⟨v, hv1, hv2, hlt⟩ := ereal_Ioo_exists_gt (a := a (Fin.init z))
        (b := b (Fin.init z)) (x := z (Fin.last (p + N))) ⟨hz2, hz3⟩
      have hvv : Fin.snoc (Fin.init z) v ∈ c := (hτ _).mpr
        ⟨by simpa using hz1, by simpa only [Fin.init_snoc, Fin.snoc_last] using hv1,
          by simpa only [Fin.init_snoc, Fin.snoc_last] using hv2⟩
      have hvf := hcgraph hvv
      rw [graphOf, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hvf
      exact absurd (hvf.trans hz'.symm) (ne_of_lt hlt).symm

/-- **The per-cell chart (explicit witness).** -/
theorem cell_chart_cont_single' (S : SOMin) {p N k : ℕ}
    (F : Family k p N) (Λ : Set (Fin p → ℝ)) (κ : Set (Fin (p + N) → ℝ))
    (Λκ : Set (Fin p → ℝ)) (hΛκ : Λκ = {l | ∃ y : Fin N → ℝ, Fin.append l y ∈ κ})
    (aΛ dΛ : ℕ) (hΛmem : Λκ ∈ S.Ω aΛ dΛ p)
    (aT : ℕ) (bT : MvPolynomial (Fin 2) ℕ) {D : ℕ}
    (Ψ : (Fin p → ℝ) → (Fin N → ℝ) → (Fin N → ℝ))
    (hΨg : ∀ j, famGraph (fun l t => Ψ l t j) ∈
      S.Ω aT (MvPolynomial.eval ![D, 1] bT) (p + N + 1))
    (hΨc : ∀ l ∈ Λκ, ∀ t ∈ openCube N, Ψ l t ∈ openCube N)
    (hΨκ : ∀ l ∈ Λκ, ∀ t ∈ openCube N, Fin.append l (Ψ l t) ∈ κ)
    (hΨs : ∀ l ∈ Λκ, ∀ y, Fin.append l y ∈ κ → ∃ t ∈ openCube N, Ψ l t = y)
    (hΨcont : ∀ l ∈ Λκ, ContinuousOn (fun t => Ψ l t) (openCube N))
    (hsub : κ ⊆ inCubeSet p N)
    (hcont : ∀ i, ContinuousOn (famFun (F i)) κ)
    (hval : ∀ (i : Fin k) (l : Fin p → ℝ), l ∈ Λ → ∀ z ∈ openCube N, F i l z ∈ Set.Ioo (0 : ℝ) 1)
    (hone : ∀ i l, ∀ z ∈ openCube N, |F i l z| ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ChartsOK S (max (max (aT + 4) (p + N + 4))
          (max (aΛ + (p + N) + (p + N) + 1 + p + 4) 5))
        (MvPolynomial.eval ![D, 0]
          (MvPolynomial.C 4 * (MvPolynomial.eval₂ MvPolynomial.C
            (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else 1) bT
            + MvPolynomial.C (dΛ + 2 + 3)))) 0 Λ F
        {fun j l t => cellChartFun Λκ Ψ l t j} ∧
      (∀ l ∈ Λ, ∀ x : Fin N → ℝ, x ∈ openCube N → Fin.append l x ∈ κ →
        ∃ t ∈ openCube N,
          ∀ i, |F i l (fun j => cellChartFun Λκ Ψ l t j) - F i l x| < ε) := by
  classical
  refine ⟨?_, ?_⟩
  · intro φ hφ
    rw [Finset.mem_singleton] at hφ
    subst hφ
    constructor
    · intro j
      set P : Set (Fin (p + N) → ℝ) := {z | (fun i : Fin p => z (Fin.castAdd N i)) ∈ Λκ} with hP
      have hPmem : P ∈ S.Ω (max (aΛ + (p + N)) ((p + N) + p) + 1 + p) (dΛ + 2) (p + N) := by
        have h := Work.WilG4c.Subst (S := S) (σ := fun i : Fin p => Fin.castAdd N i) hΛmem
        rw [hP]
        simpa [Function.comp_def] using h
      have hconst : graphOf (fun _ : Fin (p + N) → ℝ => (1 / 2 : ℝ)) ∈
          S.Ω (p + N + 1) 1 (p + N + 1) := by
        have h := S.hyp (p + N + 1)
          ((MvPolynomial.X (Fin.last (p + N)) : MvPolynomial (Fin (p + N + 1)) ℝ)
            - MvPolynomial.C (1 / 2))
        have hset : {z : Fin (p + N + 1) → ℝ |
            MvPolynomial.eval z ((MvPolynomial.X (Fin.last (p + N)) :
              MvPolynomial (Fin (p + N + 1)) ℝ) - MvPolynomial.C (1 / 2)) = 0}
            = graphOf (fun _ : Fin (p + N) → ℝ => (1 / 2 : ℝ)) := by
          ext z
          simp only [Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
            MvPolynomial.eval_C, graphOf, sub_eq_zero]
        rw [hset] at h
        refine Work.WilG1.Omega.mono h le_rfl ?_
        have htd : ((MvPolynomial.X (Fin.last (p + N)) :
            MvPolynomial (Fin (p + N + 1)) ℝ) - MvPolynomial.C (1 / 2)).totalDegree ≤ 1 := by
          refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
          rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
          omega
        omega
      have htower : graphOf (flatFun (fun l t => Ψ l t j)) ∈
          S.Ω aT (MvPolynomial.eval ![D, 1] bT) (p + N + 1) := by
        have h := hΨg j
        rwa [famGraph_eq_graphOf_flatFun] at h
      set Fc : ℕ := max (max aT (p + N)) (max (max (aΛ + (p + N)) ((p + N) + p) + 1 + p) 1)
        with hFc
      set Dc : ℕ := max (max (MvPolynomial.eval ![D, 1] bT) 1) (dΛ + 2) with hDc
      have hPmem' : P ∈ S.Ω Fc Dc (p + N) :=
        Work.WilG1.Omega.mono hPmem (by rw [hFc]; omega) (by rw [hDc]; omega)
      have hconst' : graphOf (fun _ : Fin (p + N) → ℝ => (1 / 2 : ℝ)) ∈
          S.Ω Fc Dc (p + N + 1) :=
        Work.WilG1.Omega.mono hconst (by rw [hFc]; omega) (by rw [hDc]; omega)
      have htower' : graphOf (flatFun (fun l t => Ψ l t j)) ∈ S.Ω Fc Dc (p + N + 1) :=
        Work.WilG1.Omega.mono htower (by rw [hFc]; omega) (by rw [hDc]; omega)
      have hmain := ite_graph_mem4 S (p + N) Fc Dc hPmem' htower' hconst'
      have hset : graphOf (Work.WilG4a.iteFun P (flatFun (fun l t => Ψ l t j))
          (fun _ : Fin (p + N) → ℝ => (1 / 2 : ℝ))) =
          famGraph (fun l t => (fun j l t => cellChartFun Λκ Ψ l t j) j l t) := by
        rw [famGraph_eq_graphOf_flatFun]
        congr 1
        funext z
        simp only [Work.WilG4a.iteFun, flatFun, cellChartFun, hP]
        by_cases h : (fun i : Fin p => z (Fin.castAdd N i)) ∈ Λκ <;> simp [h]
      rw [hset] at hmain
      refine Work.WilG1.Omega.mono hmain ?_ ?_
      · rw [hFc]
        omega
      · have hsub' : MvPolynomial.eval ![D, 0] (MvPolynomial.eval₂ MvPolynomial.C
            (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else 1) bT)
            = MvPolynomial.eval ![D, 1] bT := by
          rw [Work.WilkG4c.eval_eval₂_C_nat]
          have hfun : (fun s : Fin 2 => MvPolynomial.eval ![D, 0]
              (if s = 0 then MvPolynomial.X 0 else 1)) = ![D, 1] := by
            funext i
            fin_cases i <;> simp
          rw [hfun]
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_add,
          MvPolynomial.eval_C, hsub', hDc]
        omega
    · intro l hl
      constructor
      · intro t ht
        change cellChartFun Λκ Ψ l t ∈ openCube N
        by_cases h : l ∈ Λκ
        · rw [cellChartFun_of_mem h t]
          exact hΨc l h t ht
        · rw [cellChartFun_of_not_mem h t]
          exact const_half_mem_openCube N
      · intro i
        constructor
        · by_cases h : l ∈ Λκ
          · have hslice : ContinuousOn (fun z : Fin N → ℝ => F i l z)
                {z : Fin N → ℝ | Fin.append l z ∈ κ} := by
              have h1 : ContinuousOn (fun z : Fin N → ℝ => famFun (F i) (Fin.append l z))
                  {z : Fin N → ℝ | Fin.append l z ∈ κ} :=
                (hcont i).comp (continuous_fin_append (p := p) l).continuousOn (fun z hz => hz)
              refine h1.congr (fun z hz => ?_)
              simp only [Function.comp_apply, famFun, Fin.append_left, Fin.append_right]
            have hcomp := hslice.comp (hΨcont l h) (fun t ht => hΨκ l h t ht)
            refine contDiffOn_zero.mpr (hcomp.congr (fun t ht => ?_))
            change F i l (fun j => cellChartFun Λκ Ψ l t j) = F i l (Ψ l t)
            congr 1
            exact cellChartFun_of_mem h t
          · have hconst'' : ContinuousOn (fun t : Fin N → ℝ =>
                F i l (fun j => cellChartFun Λκ Ψ l t j)) (openCube N) := by
              refine (continuousOn_const (c := F i l (fun _ => (1 / 2 : ℝ)))).congr
                (fun t ht => ?_)
              change F i l (fun j => cellChartFun Λκ Ψ l t j) = F i l (fun _ => (1 / 2 : ℝ))
              congr 1
              exact cellChartFun_of_not_mem h t
            exact contDiffOn_zero.mpr hconst''
        · intro m hm t ht
          have hm0 : m = 0 := by omega
          subst hm0
          rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
          apply hone i l
          change cellChartFun Λκ Ψ l t ∈ openCube N
          by_cases h : l ∈ Λκ
          · rw [cellChartFun_of_mem h t]
            exact hΨc l h t ht
          · rw [cellChartFun_of_not_mem h t]
            exact const_half_mem_openCube N
  · intro l hl x hx hmem
    have hlx : l ∈ Λκ := by
      rw [hΛκ]
      exact ⟨x, hmem⟩
    obtain ⟨t, ht, htx⟩ := hΨs l hlx x hmem
    refine ⟨t, ht, ?_⟩
    intro i
    have hval' : (fun j => cellChartFun Λκ Ψ l t j) = x := by
      rw [cellChartFun_of_mem hlx t]
      exact htx
    rw [hval']
    simpa using hε

/-- **Composition of a degree bound with a univariate polynomial.** -/
theorem polyCompEval' (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ) :
    ∃ B : MvPolynomial (Fin 2) ℕ, ∀ D : ℕ,
      MvPolynomial.eval ![D, 0] B = MvPolynomial.eval ![(c.eval D), 1] b := by
  let p : MvPolynomial (Fin 2) ℕ := Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) c
  refine ⟨MvPolynomial.bind₁ (fun i : Fin 2 => if i = 0 then p else MvPolynomial.C 1) b, ?_⟩
  intro D
  have hp : MvPolynomial.eval ![D, 0] p = c.eval D := by
    have hcomp : (MvPolynomial.eval (fun i : Fin 2 => ![D, 0] i)).comp
        (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)) =
        Polynomial.eval₂RingHom (RingHom.id ℕ) D := by
      refine Polynomial.ringHom_ext ?_ ?_
      · intro a
        simp [Polynomial.eval₂RingHom]
      · simp [Polynomial.eval₂RingHom]
    have := RingHom.congr_fun hcomp c
    change MvPolynomial.eval (fun i : Fin 2 => ![D, 0] i)
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) c) =
        Polynomial.eval₂ (RingHom.id ℕ) D c at this
    simpa [p] using this
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℕ) ![D, 0]
    (fun i : Fin 2 => if i = 0 then p else MvPolynomial.C 1) b
  have hfun : (fun i : Fin 2 => MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, 0]
      (if i = 0 then p else MvPolynomial.C 1)) = ![(c.eval D), 1] := by
    funext i
    fin_cases i
    · simpa using hp
    · simp
  rw [hfun] at h
  exact h

end Work.WilG4c
