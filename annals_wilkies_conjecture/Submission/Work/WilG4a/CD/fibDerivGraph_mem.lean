/-
  WilG4a / CD / `fibDerivGraph_mem` — the target of this file.

  For a `p`-parameter family `f : ℝ^p → ℝ → ℝ` whose graph is `Ω F0 D (p+2)`-definable, the set

    `T_j(f) = {w : ℝ^{p+2} | the slice `f (init (init w))` is `C^j` at `w (last p)` and
              `w (last (p+1))` is its `j`-th derivative}`

  is `Ω a (b.eval ![D,j]) (p+2)` with `a, b` depending only on `p` and `F0`.

  ## Proof

  Strong induction on the number of parameters `p`.  Given `f`, `D`, `j`:

  * `fibGerm_mem` provides the fibre-germ locus `Γ = fibGerm f j` (the points whose punctured
    fibre neighbourhood lies in the joint `C^j` locus) as an `Ω`-set, and
    `fibMainSet_mem_of_germ` packages the four conjuncts of the `Ω`-approximation
    `R = fibMainSet f j`.
  * `cellDecomp_germ` provides a cylindrical decomposition of `ℝ^{p+1}` refining the thin bad
    locus `V_j = badLocus f j`, with the extra property that over every *thick* base cell the
    fibre-germ `Γ` holds everywhere.
  * The base decomposition of `ℝ^p` splits into the *fat* cells (non-empty interior) and the
    *thin* cells (empty interior).  Over the fat cells, `T_j(f)` coincides with `R`
    (`fibDerivSet_eq_fibMainSet_on_germ`, using `Γ`), and over a thin cell `C` the
    parametrisation `thinCellParam` exhibits the family over the tube `C × ℝ` as a pullback of a
    family with `k < p` parameters (`graphFam_param_mem`), to which the induction hypothesis
    applies; `fibDerivSet_lift` identifies the lifted set with `T_j(f)` over `C`.
  * The two parts are `Ω`-combinations of the ingredients, and the degree bound is a polynomial
    in `(D, j)` because the cell count is bounded by `bC.eval ![D,j]`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG0.API
import Submission.Work.WilG4a.exists_cell_partition_refining
import Submission.Work.WilG4a.CD.fibDerivDefs
import Submission.Work.WilG4a.CD.fibSetMem
import Submission.Work.WilG4a.CD.fibGerm_mem
import Submission.Work.WilG4a.CD.fibDerivSet_eq_fibMainSet_on_germ
import Submission.Work.WilG4a.CD.cellDecomp_germ
import Submission.Work.WilG4a.CD.thinCellParam
import Submission.Work.WilG4a.CD.graphFam_param_mem
import Submission.Work.WilG4a.CD.fibDerivSet_lift

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG4a.CD
open WilkiesDesign

/-! ## Auxiliary lemmas -/

theorem projLast_eq_image_init {n : ℕ} (A : Set (Fin (n + 1) → ℝ)) :
    projLast A = Fin.init '' A := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨Fin.snoc x t, ht, by simp⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z (Fin.last n), by rw [Fin.snoc_init_self]; exact hz⟩

theorem image_init_mem {S : WilkiesDesign.SOMin} {n F D : ℕ} {X : Set (Fin (n + 1) → ℝ)}
    (h : X ∈ S.Ω F D (n + 1)) : Fin.init '' X ∈ S.Ω (F + 1) D n := by
  rw [← projLast_eq_image_init X]
  exact S.proj h

theorem union_finset_mem {S : WilkiesDesign.SOMin} {n : ℕ} {σ : Type*} (s : Finset σ)
    (A : σ → Set (Fin n → ℝ)) {F D : ℕ} (h : ∀ i ∈ s, A i ∈ S.Ω F D n) :
    (⋃ i ∈ s, A i) ∈ S.Ω F (s.card * D) n := by
  classical
  set e : ↥s ≃ Fin (Fintype.card ↥s) := Fintype.equivFin ↥s with he
  set A' : Fin (Fintype.card ↥s) → Set (Fin n → ℝ) := fun i => A ((e.symm i : ↥s) : σ) with hA'
  have hmem : ∀ i, A' i ∈ S.Ω F D n := fun i => h _ (e.symm i).2
  have hunion := S.union (fun _ : Fin (Fintype.card ↥s) => D) A' hmem
  have hset : (⋃ i : Fin (Fintype.card ↥s), A' i) = ⋃ i ∈ s, A i := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion₂.mpr ⟨((e.symm i : ↥s) : σ), (e.symm i).2, hi⟩
    · intro hz
      obtain ⟨i, hi, hi2⟩ := Set.mem_iUnion₂.mp hz
      refine Set.mem_iUnion.mpr ⟨e ⟨i, hi⟩, ?_⟩
      have h1 : A' (e ⟨i, hi⟩) = A i := by simp [hA']
      rwa [h1]
  rw [hset] at hunion
  have hsum : (∑ _ : Fin (Fintype.card ↥s), D) = s.card * D := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe]
  rw [hsum] at hunion
  exact hunion

/-- Substituting the second variable of a two-variable polynomial by another polynomial. -/
theorem eval_bind_one {b g : MvPolynomial (Fin 2) ℕ} (D j : ℕ) :
    MvPolynomial.eval ![D, MvPolynomial.eval ![D, j] g] b =
      MvPolynomial.eval ![D, j]
        (MvPolynomial.bind₁ (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else g) b) := by
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℕ) ![D, j]
    (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else g) b
  have hfun : (fun i : Fin 2 => MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, j]
      (if i = 0 then MvPolynomial.X 0 else g)) = ![D, MvPolynomial.eval ![D, j] g] := by
    funext i; fin_cases i <;> simp
  rw [hfun] at h
  change MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, MvPolynomial.eval ![D, j] g] b =
    MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, j]
      (MvPolynomial.bind₁ (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else g) b)
  exact h.symm

/-! ## The inductive step -/

private theorem fibDerivGraph_aux (S : WilkiesDesign.SOMin) (hcd : WilkiesDesign.SOMin.SharpCD S)
    (hder : WilkiesDesign.SOMin.SharpDeriv S) :
    ∀ p F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        fibDerivSet f j ∈ S.Ω a (MvPolynomial.eval ![D, j] b) (p + 2) := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro F0
    obtain ⟨aG, bG, hgerm⟩ := fibGerm_mem (S := S) hder p F0
    obtain ⟨aR, bR, hR⟩ := fibMainSet_mem_of_germ (S := S) hder p F0 aG bG hgerm
    obtain ⟨aC, bC, hDec⟩ := cellDecomp_germ S hcd hder p F0
    obtain ⟨aP, bP, hP⟩ := thinCellParam S hcd p (aC + 1)
    choose A B hAB using fun k : Fin p => graphFam_param_mem (S := S) hcd p (k : ℕ) F0 aP
    choose aT bT hT using fun k : Fin p => ih (k : ℕ) k.isLt (A k)
    -- the polynomial `bP.eval (bC.eval ![D,j])`, read as a two-variable polynomial
    set P₁ : MvPolynomial (Fin 2) ℕ := Polynomial.eval₂ MvPolynomial.C bC bP with hP₁
    have hP₁eval : ∀ D j : ℕ,
        MvPolynomial.eval ![D, j] P₁ = bP.eval (MvPolynomial.eval ![D, j] bC) := by
      intro D j; rw [hP₁]; exact eval_eval₂_C bC bP D j
    -- the per-`k` degree polynomial of a lifted thin-cell contribution
    have hPdata : ∀ k : Fin p, ∃ βk : MvPolynomial (Fin 2) ℕ,
        ∀ D j : ℕ, MvPolynomial.eval ![D, j] βk =
          (bT k).eval ![MvPolynomial.eval ![D, bP.eval (MvPolynomial.eval ![D, j] bC)] (B k), j]
            + 2 + MvPolynomial.eval ![D, j] bC := by
      intro k
      set P₂ : MvPolynomial (Fin 2) ℕ :=
        MvPolynomial.bind₁ (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else P₁) (B k)
        with hP₂
      have hP₂eval : ∀ D j : ℕ, MvPolynomial.eval ![D, j] P₂ =
          (B k).eval ![D, bP.eval (MvPolynomial.eval ![D, j] bC)] := by
        intro D j
        rw [hP₂, ← eval_bind_one D j, hP₁eval D j]
      obtain ⟨P₃, hP₃⟩ := exists_eval_comp (bT k) P₂
      refine ⟨P₃ + MvPolynomial.C 2 + bC, fun D j => ?_⟩
      rw [MvPolynomial.eval_add, MvPolynomial.eval_add, ← hP₂eval D j, ← hP₃ D j]
      simp
    choose βk hβk using hPdata
    refine ⟨(aR + (aC + 3) + 1 + 1)
        + (∑ k : Fin p, (aT k + 2 * ((p + 2) + ((k : ℕ) + 2)) + 1 + (aC + 3) + 1 + 1)) + 1,
      (bR + bC * bC) + bC * (∑ k : Fin p, βk k), ?_⟩
    intro D j f hf
    -- the decomposition and its base
    obtain ⟨C, hCyl, hCcard, hCΩ, hCref, hCgerm⟩ := hDec D j hf
    set Bs : Finset (Set (Fin p → ℝ)) := C.image (fun κ => Fin.init '' κ) with hBs
    have hBcyl : WilkiesDesign.IsCylDecomp p Bs := hCyl.2.2.2
    have hBcell : ∀ c ∈ Bs, WilkiesDesign.IsCell p c := fun c hc => cylDecomp_isCell p hBcyl c hc
    have hBΩ : ∀ c ∈ Bs, c ∈ S.Ω (aC + 1) (MvPolynomial.eval ![D, j] bC) p := by
      intro c hc
      obtain ⟨κ, hκ, hκeq⟩ := Finset.mem_image.mp hc
      rw [← hκeq, ← projLast_eq_image_init κ]
      exact S.proj (hCΩ κ hκ)
    -- the base cell containing a parameter, together with the germ property
    have hgermAt : ∀ (l : Fin p → ℝ) (x : ℝ), (∃ c ∈ Bs, l ∈ c) → (∃ c ∈ Bs, l ∈ c ∧ (interior c).Nonempty)
        → fibGerm f j (Fin.snoc l x) := by
      rintro l x _ ⟨c, hc, hlc, hcint⟩
      obtain ⟨κ, hκ, hκeq⟩ := Finset.mem_image.mp hc
      have := hCgerm κ hκ (by rwa [hκeq]) l (by rwa [hκeq]) x
      exact this
    set Fat := Bs.filter (fun c => (interior c).Nonempty) with hFat
    set Thin := Bs.filter (fun c => interior c = ∅) with hThin
    -- the fat part
    have hFatcover : (⋃ c ∈ Fat, c) ∈ S.Ω (aC + 1) ((bC * bC).eval ![D, j]) p := by
      have h1 : (⋃ c ∈ Fat, c) ∈ S.Ω (aC + 1) (Fat.card * MvPolynomial.eval ![D, j] bC) p :=
        union_finset_mem (S := S) Fat (fun c => c)
          (fun c hc => hBΩ c (Finset.mem_filter.mp hc).1)
      refine Work.WilG0.Omega_mono_FD le_rfl ?_ h1
      have hcard : Fat.card ≤ MvPolynomial.eval ![D, j] bC :=
        le_trans (le_trans (Finset.card_le_card (Finset.filter_subset _ _))
          Finset.card_image_le) hCcard
      rw [MvPolynomial.eval_mul]
      exact Nat.mul_le_mul_right _ hcard
    have hFatLift : {w : Fin (p + 2) → ℝ | Fin.init (Fin.init w) ∈ (⋃ c ∈ Fat, c)} ∈
        S.Ω (aC + 3) ((bC * bC).eval ![D, j]) (p + 2) :=
      S.prod_right (S.prod_right hFatcover)
    have hFatPart : fibMainSet f j ∩ {w : Fin (p + 2) → ℝ |
        Fin.init (Fin.init w) ∈ (⋃ c ∈ Fat, c)} ∈
        S.Ω (aR + (aC + 3) + 1 + 1)
          (MvPolynomial.eval ![D, j] bR + MvPolynomial.eval ![D, j] (bC * bC)) (p + 2) := by
      have h1 := Work.WilG0.Omega_mono_FD (F' := aR + (aC + 3) + 1) (by omega) le_rfl (hR D j hf)
      have h2 := Work.WilG0.Omega_mono_FD (F' := aR + (aC + 3) + 1) (by omega) le_rfl hFatLift
      exact Work.WilG0.Omega_inter2 h1 h2
    have hFatPart' : fibMainSet f j ∩ {w : Fin (p + 2) → ℝ |
        Fin.init (Fin.init w) ∈ (⋃ c ∈ Fat, c)} ∈
        S.Ω (aR + (aC + 3) + 1 + 1)
          (MvPolynomial.eval ![D, j] (bR + bC * bC)) (p + 2) := by
      refine Work.WilG0.Omega_mono_FD le_rfl ?_ hFatPart
      rw [MvPolynomial.eval_add]
    -- the thin part
    have hThinLift : ∀ c ∈ Thin, ∃ L : Set (Fin (p + 2) → ℝ),
        L ∈ S.Ω (∑ k : Fin p, (aT k + 2 * ((p + 2) + ((k : ℕ) + 2)) + 1 + (aC + 3) + 1 + 1))
              (MvPolynomial.eval ![D, j] (∑ k : Fin p, βk k)) (p + 2) ∧
        L = fibDerivSet f j ∩ {w : Fin (p + 2) → ℝ | Fin.init (Fin.init w) ∈ c} := by
      intro c hc
      have hcB : c ∈ Bs := (Finset.mem_filter.mp hc).1
      have hcthin : interior c = ∅ := (Finset.mem_filter.mp hc).2
      obtain ⟨k, hk, e, Ψ, hsec, hPar⟩ :=
        hP (MvPolynomial.eval ![D, j] bC) c (hBΩ c hcB) (hBcell c hcB) hcthin
      have hgraph := hAB ⟨k, hk⟩ D (bP.eval (MvPolynomial.eval ![D, j] bC)) f Ψ hf hPar
      have hT1 := hT ⟨k, hk⟩
        (MvPolynomial.eval ![D, bP.eval (MvPolynomial.eval ![D, j] bC)] (B ⟨k, hk⟩)) j hgraph
      have hS := Work.WilG4a.subst_mem (S := S) (cutIdx p k e) hT1
      have hCL : {w : Fin (p + 2) → ℝ | Fin.init (Fin.init w) ∈ c} ∈
          S.Ω (aC + 3) (MvPolynomial.eval ![D, j] bC) (p + 2) :=
        S.prod_right (S.prod_right (hBΩ c hcB))
      have hcomb : ({x : Fin (p + 2) → ℝ |
            x ∘ cutIdx p k e ∈ fibDerivSet (fun (u : Fin k → ℝ) (x : ℝ) => f (Ψ u) x) j} ∩
          {w : Fin (p + 2) → ℝ | Fin.init (Fin.init w) ∈ c}) ∈
          S.Ω ((aT ⟨k, hk⟩ + 2 * ((p + 2) + (k + 2)) + 1) + (aC + 3) + 1 + 1)
            ((bT ⟨k, hk⟩).eval
                ![MvPolynomial.eval ![D, bP.eval (MvPolynomial.eval ![D, j] bC)] (B ⟨k, hk⟩), j]
              + 2 + MvPolynomial.eval ![D, j] bC) (p + 2) := by
        have h1 := Work.WilG0.Omega_mono_FD
          (F' := (aT ⟨k, hk⟩ + 2 * ((p + 2) + (k + 2)) + 1) + (aC + 3) + 1) (by omega) le_rfl hS
        have h2 := Work.WilG0.Omega_mono_FD
          (F' := (aT ⟨k, hk⟩ + 2 * ((p + 2) + (k + 2)) + 1) + (aC + 3) + 1) (by omega) le_rfl hCL
        exact Work.WilG0.Omega_inter2 h1 h2
      refine ⟨{x : Fin (p + 2) → ℝ |
            x ∘ cutIdx p k e ∈ fibDerivSet (fun (u : Fin k → ℝ) (x : ℝ) => f (Ψ u) x) j} ∩
          {w : Fin (p + 2) → ℝ | Fin.init (Fin.init w) ∈ c}, ?_, ?_⟩
      · refine Work.WilG0.Omega_mono_FD ?_ ?_ hcomb
        · exact Finset.single_le_sum (f := fun kk : Fin p =>
              (aT kk + 2 * ((p + 2) + ((kk : ℕ) + 2)) + 1 + (aC + 3) + 1 + 1))
            (fun i _ => Nat.zero_le _) (Finset.mem_univ (⟨k, hk⟩ : Fin p))
        · rw [← hβk ⟨k, hk⟩ D j, MvPolynomial.eval_sum]
          exact Finset.single_le_sum (f := fun kk : Fin p =>
              MvPolynomial.eval ![D, j] (βk kk))
            (fun i _ => Nat.zero_le _) (Finset.mem_univ (⟨k, hk⟩ : Fin p))
      · ext w
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨(fibDerivSet_lift e c Ψ hsec f j w h2).mpr h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨(fibDerivSet_lift e c Ψ hsec f j w h2).mp h1, h2⟩
    choose L hL using hThinLift
    let Lf : Set (Fin p → ℝ) → Set (Fin (p + 2) → ℝ) :=
      fun c => if h : c ∈ Thin then L c h else ∅
    have hLf : ∀ c ∈ Thin, Lf c ∈
        S.Ω (∑ k : Fin p, (aT k + 2 * ((p + 2) + ((k : ℕ) + 2)) + 1 + (aC + 3) + 1 + 1))
          (MvPolynomial.eval ![D, j] (∑ k : Fin p, βk k)) (p + 2) ∧
        Lf c = fibDerivSet f j ∩ {w : Fin (p + 2) → ℝ | Fin.init (Fin.init w) ∈ c} := by
      intro c hc
      simp only [Lf, dif_pos hc]
      exact hL c hc
    have hThinPart : (⋃ c ∈ Thin, Lf c) ∈
        S.Ω (∑ k : Fin p, (aT k + 2 * ((p + 2) + ((k : ℕ) + 2)) + 1 + (aC + 3) + 1 + 1))
          (Thin.card * MvPolynomial.eval ![D, j] (∑ k : Fin p, βk k)) (p + 2) :=
      union_finset_mem Thin Lf (fun c hc => (hLf c hc).1)
    have hThinPart' : (⋃ c ∈ Thin, Lf c) ∈
        S.Ω (∑ k : Fin p, (aT k + 2 * ((p + 2) + ((k : ℕ) + 2)) + 1 + (aC + 3) + 1 + 1))
          (MvPolynomial.eval ![D, j] (bC * (∑ k : Fin p, βk k))) (p + 2) := by
      refine Work.WilG0.Omega_mono_FD le_rfl ?_ hThinPart
      have hcard : Thin.card ≤ MvPolynomial.eval ![D, j] bC :=
        le_trans (le_trans (Finset.card_le_card (Finset.filter_subset _ _))
          Finset.card_image_le) hCcard
      rw [MvPolynomial.eval_mul]
      exact Nat.mul_le_mul_right _ hcard
    -- the union of the two parts
    have h1 := Work.WilG0.Omega_mono_FD
      (F' := (aR + (aC + 3) + 1 + 1)
        + (∑ k : Fin p, (aT k + 2 * ((p + 2) + ((k : ℕ) + 2)) + 1 + (aC + 3) + 1 + 1)) + 1)
      (by omega) le_rfl hFatPart'
    have h2 := Work.WilG0.Omega_mono_FD
      (F' := (aR + (aC + 3) + 1 + 1)
        + (∑ k : Fin p, (aT k + 2 * ((p + 2) + ((k : ℕ) + 2)) + 1 + (aC + 3) + 1 + 1)) + 1)
      (by omega) le_rfl hThinPart'
    have hU := Work.WilG0.Omega_union2 h1 h2
    -- the set identity
    have hset : fibDerivSet f j =
        (fibMainSet f j ∩ {w : Fin (p + 2) → ℝ | Fin.init (Fin.init w) ∈ (⋃ c ∈ Fat, c)})
          ∪ (⋃ c ∈ Thin, Lf c) := by
      ext w
      set l : Fin p → ℝ := Fin.init (Fin.init w) with hl
      have hcover : ∃ c ∈ Bs, l ∈ c := cylDecomp_exists_mem p hBcyl l
      constructor
      · intro hw
        obtain ⟨c, hc, hlc⟩ := hcover
        by_cases hci : (interior c).Nonempty
        · have hthin : c ∈ Fat := Finset.mem_filter.mpr ⟨hc, hci⟩
          obtain ⟨κ, hκ, hκeq⟩ := Finset.mem_image.mp hc
          have hΓ : Fin.init w ∈ fibGerm f j := by
            have h2 := hCgerm κ hκ (by rwa [hκeq]) l (by rwa [hκeq])
              ((Fin.init w) (Fin.last p))
            rw [hl, Fin.snoc_init_self (Fin.init w)] at h2
            exact h2
          exact Or.inl ⟨(fibDerivSet_eq_fibMainSet_on_germ p f j w hΓ).mp hw,
            Set.mem_iUnion₂.mpr ⟨c, hthin, hlc⟩⟩
        · have hcc : c ∈ Thin := Finset.mem_filter.mpr ⟨hc, Set.not_nonempty_iff_eq_empty.mp hci⟩
          exact Or.inr (Set.mem_iUnion₂.mpr ⟨c, hcc, by
            rw [(hLf c hcc).2]
            exact ⟨hw, hlc⟩⟩)
      · rintro (⟨hmem, hfat⟩ | hthin)
        · obtain ⟨c, hc, hlc⟩ := Set.mem_iUnion₂.mp hfat
          have hci : (interior c).Nonempty := (Finset.mem_filter.mp hc).2
          have hcB : c ∈ Bs := (Finset.mem_filter.mp hc).1
          obtain ⟨κ, hκ, hκeq⟩ := Finset.mem_image.mp hcB
          have hΓ : Fin.init w ∈ fibGerm f j := by
            have h2 := hCgerm κ hκ (by rwa [hκeq]) l (by rwa [hκeq])
              ((Fin.init w) (Fin.last p))
            rw [hl, Fin.snoc_init_self (Fin.init w)] at h2
            exact h2
          exact (fibDerivSet_eq_fibMainSet_on_germ p f j w hΓ).mpr hmem
        · obtain ⟨c, hc, hlc⟩ := Set.mem_iUnion₂.mp hthin
          rw [(hLf c hc).2] at hlc
          exact hlc.1
    rw [hset]
    refine Work.WilG0.Omega_mono_FD (by omega) (le_of_eq ?_) hU
    simp only [MvPolynomial.eval_add]

theorem fibDerivGraph_mem (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        {w : Fin (p + 2) → ℝ | ContDiffAt ℝ j (fun x : ℝ => f (Fin.init (Fin.init w)) x) ((Fin.init w) (Fin.last p)) ∧
          w (Fin.last (p + 1)) = iteratedDeriv j (fun x : ℝ => f (Fin.init (Fin.init w)) x) ((Fin.init w) (Fin.last p))} ∈
          S.Ω a (MvPolynomial.eval ![D, j] b) (p + 2) :=
  fibDerivGraph_aux S hcd hder p F0

end Work.WilG4a.CD
