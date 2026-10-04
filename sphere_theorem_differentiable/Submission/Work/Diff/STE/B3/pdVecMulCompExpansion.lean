import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `pdVecMulCompExpansion`: the Leibniz/Faà di Bruno expansion of `∂^l (g · (v ∘ T))`

For smooth `T : (ι → ℝ) → (ι → ℝ)`, smooth `g : (ι → ℝ) → ℂ` and every order `m` and list of
directions `l : Fin m → ι`, the iterated derivative

`∂^l (fun z ↦ g z · v (T z))`

of the product of `g` with the pull-back of `v` along `T` is a finite sum

`∑ i, c i z · ∂^{dir i} v (T z)`

in which the coefficients `c i` are smooth, vanish outside `tsupport g`, and the order
`ord i` of the transported derivative of `v` never exceeds `m`.

The proof is an induction on the order, peeling the *first* direction `l 0`:

* the inner `m`-fold derivative is expanded by the induction hypothesis (`e.expand`);
* `∂` is applied to the resulting finite sum of products (`pd_sum`), each product is
  differentiated by the Leibniz rule (`pd_mul_fn`), and the composition `v ∘ T` is differentiated
  by the chain rule (`pd_comp_eq`), which distributes the new derivative over the coordinates of
  `fderiv ℝ T z (Pi.single (l 0) 1)`.  A single step therefore produces, for every index `j` of
  the old family, one term with the derivative falling on the coefficient `c j` (order `ord j`) and
  `Fintype.card ι` terms with one more derivative on `v` (order `ord j + 1`, direction
  `Fin.cons p (dir j)`).

The support condition is carried in the slightly stronger "eventually zero" form
`c i =ᶠ[𝓝 z] 0` for `z ∉ tsupport g`, which is stable under `pd` (`pd_eventuallyEq_zero`); the
statement of the target theorem follows pointwise.

One subtlety of the formalisation: the index type of the new family must be a *small* type
(`Type 0`, as required by the statement), so the coordinate index `ι` is replaced by the equivalent
`Fin (Fintype.card ι)` (`eι`), and the coordinate sum is re-indexed with `Equiv.sum_comp`.
-/

noncomputable section

open Filter

namespace Work.Diff.STE.B3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Auxiliary facts about `pd` and `pdVec` -/

/-- **Peeling the first direction**: `∂^{l₀ l₁ … l_{m-1}} = ∂_{l₀} ∂^{l₁ … l_{m-1}}`. -/
lemma pdMulComp_pdVec_succ_cons (m : ℕ) (l : Fin (m + 1) → ι) (f : (ι → ℝ) → ℂ) :
    Work.Diff.STE.pdVec (m + 1) l f = Work.Diff.STE.pd (l 0) (Work.Diff.STE.pdVec m (Fin.tail l) f) := by
  have h : List.ofFn l = l 0 :: List.ofFn (Fin.tail l) := by
    conv_lhs => rw [← Fin.cons_self_tail l]
    rw [List.ofFn_cons]
  simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
  rw [h, List.foldr_cons]

/-- **Adding a direction** (at the front): `∂_p (∂^{d} v) = ∂^{(p, d)} v`. -/
lemma pdMulComp_pd_pdVec_cons (k : ℕ) (p : ι) (d : Fin k → ι) (v : (ι → ℝ) → ℂ) :
    Work.Diff.STE.pd p (Work.Diff.STE.pdVec k d v) = Work.Diff.STE.pdVec (k + 1) (Fin.cons p d) v := by
  simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_cons, List.foldr_cons]

/-- A continuous linear functional on `ι → ℝ` is determined by its values on the standard basis. -/
lemma pdMulComp_clm_eq_sum_single (L : (ι → ℝ) →L[ℝ] ℂ) (y : ι → ℝ) :
    L y = ∑ p, (y p : ℂ) * L (Pi.single p 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [show Pi.single p (y p) = y p • Pi.single p (1 : ℝ) by
        rw [← Pi.single_smul]; simp [smul_eq_mul]]
  rw [map_smul, Complex.real_smul]

/-- **Chain rule** for `pd` along a map `T`: the derivative of `w ∘ T` at `z` is the derivative of
`w` at `T z` evaluated on `fderiv ℝ T z (Pi.single i 1)`, expanded in the standard basis. -/
lemma pdMulComp_pd_comp_eq {T : (ι → ℝ) → (ι → ℝ)} (hT : Differentiable ℝ T) (i : ι)
    {w : (ι → ℝ) → ℂ} (hw : Differentiable ℝ w) :
    Work.Diff.STE.pd i (fun z => w (T z))
      = fun z => ∑ p, (((fderiv ℝ T z) (Pi.single i 1)) p : ℂ) * Work.Diff.STE.pd p w (T z) := by
  funext z
  have hcomp : HasFDerivAt (fun z => w (T z)) ((fderiv ℝ w (T z)).comp (fderiv ℝ T z)) z :=
    ((hw (T z)).hasFDerivAt).comp z ((hT z).hasFDerivAt)
  have h1 : fderiv ℝ (fun z => w (T z)) z = (fderiv ℝ w (T z)).comp (fderiv ℝ T z) :=
    hcomp.fderiv
  rw [Work.Diff.STE.pd, h1, ContinuousLinearMap.comp_apply]
  exact pdMulComp_clm_eq_sum_single (fderiv ℝ w (T z)) ((fderiv ℝ T z) (Pi.single i 1))

/-- Linearity of `pd` in a finite sum. -/
lemma pdMulComp_pd_sum {α : Type*} [Fintype α] (i : ι) (F : α → (ι → ℝ) → ℂ)
    (hF : ∀ j, Differentiable ℝ (F j)) (z : ι → ℝ) :
    Work.Diff.STE.pd i (fun y => ∑ j, F j y) z = ∑ j, Work.Diff.STE.pd i (F j) z := by
  have hsum : (fun y => ∑ j, F j y) = ∑ j : α, F j := by
    funext y; rw [Finset.sum_apply]
  simp only [Work.Diff.STE.pd]
  rw [hsum, fderiv_sum (u := Finset.univ) (A := F) (fun j _ => hF j z)]
  exact sum_apply Finset.univ (fun j => fderiv ℝ (F j) z) (Pi.single i 1)

/-- Smoothness of `pd`. -/
lemma pdMulComp_contDiff_pd (i : ι) {c : (ι → ℝ) → ℂ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd i c) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ c) := hc.fderiv_right (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => (fderiv ℝ c x) (Pi.single i (1 : ℝ))) :=
    h1.clm_apply (contDiff_const (𝕜 := ℝ) (E := ι → ℝ) (F := ι → ℝ) (n := (⊤ : ℕ∞))
      (c := Pi.single i (1 : ℝ)))
  convert h2 using 1
  funext x
  simp [Work.Diff.STE.pd]

/-- Smoothness of `pdVec`. -/
lemma pdMulComp_contDiff_pdVec : ∀ (k : ℕ) (d : Fin k → ι) {v : (ι → ℝ) → ℂ},
    ContDiff ℝ (⊤ : ℕ∞) v → ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdVec k d v) := by
  intro k
  induction k with
  | zero =>
    intro d v hv
    simpa [Work.Diff.STE.pdVec, Work.Diff.STE.pdList] using hv
  | succ k ih =>
    intro d v hv
    rw [pdMulComp_pdVec_succ_cons k d v]
    exact pdMulComp_contDiff_pd (d 0) (ih (Fin.tail d) hv)

/-- A function which vanishes on a neighbourhood of `z` has vanishing `pd` at `z`. -/
lemma pdMulComp_pd_eq_zero_of_eventuallyEq_zero {i : ι} {f : (ι → ℝ) → ℂ} {z : ι → ℝ}
    (h : f =ᶠ[nhds z] 0) : Work.Diff.STE.pd i f z = 0 := by
  have h1 : fderiv ℝ f z = fderiv ℝ (0 : (ι → ℝ) → ℂ) z := h.fderiv_eq
  simp [Work.Diff.STE.pd, h1]

/-- The "eventually zero" form of the support condition is stable under `pd`. -/
lemma pdMulComp_pd_eventuallyEq_zero {i : ι} {f : (ι → ℝ) → ℂ} {z : ι → ℝ}
    (h : f =ᶠ[nhds z] 0) : Work.Diff.STE.pd i f =ᶠ[nhds z] 0 := by
  rcases mem_nhds_iff.mp h with ⟨U, hUf, hUopen, hzU⟩
  filter_upwards [hUopen.mem_nhds hzU] with y hy
  exact pdMulComp_pd_eq_zero_of_eventuallyEq_zero
    (Filter.eventually_of_mem (hUopen.mem_nhds hy) (fun y' hy' => hUf hy'))

/-- Leibniz rule for `pd`, function level. -/
lemma pdMulComp_pd_mul (i : ι) (f g : (ι → ℝ) → ℂ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    Work.Diff.STE.pd i (f * g) = f * Work.Diff.STE.pd i g + g * Work.Diff.STE.pd i f := by
  funext x
  have h := fderiv_mul (hf x) (hg x)
  have h2 : (fderiv ℝ (f * g) x) (Pi.single i 1)
      = f x * ((fderiv ℝ g x) (Pi.single i 1)) + g x * ((fderiv ℝ f x) (Pi.single i 1)) := by
    rw [h]; simp [smul_eq_mul]
  simpa [Work.Diff.STE.pd] using h2

/-- Smoothness of the coordinate functions of `fderiv ℝ T`. -/
lemma pdMulComp_contDiff_coord_fderiv {T : (ι → ℝ) → (ι → ℝ)} (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (i j : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => (((fderiv ℝ T z) (Pi.single i (1 : ℝ))) j : ℂ)) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ T) := hT.fderiv_right (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => (fderiv ℝ T x) (Pi.single i (1 : ℝ))) :=
    h1.clm_apply (contDiff_const (𝕜 := ℝ) (E := ι → ℝ) (F := ι → ℝ) (n := (⊤ : ℕ∞))
      (c := Pi.single i (1 : ℝ)))
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ι → ℝ => ((fderiv ℝ T x) (Pi.single i (1 : ℝ))) j) := by
    have hp : ContDiff ℝ (⊤ : ℕ∞) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) :=
      ContinuousLinearMap.contDiff _
    exact hp.comp h2
  exact Complex.ofRealCLM.contDiff.comp h3

/-! ## The expansion data -/

/-- The data of the expansion of `∂^l (g · (v ∘ T))` as `∑ i, c i z · ∂^{dir i} v (T z)`, with the
support condition of `c` in the "eventually zero off `tsupport g`" form (stable under `pd`). -/
structure PDExp (T : (ι → ℝ) → (ι → ℝ)) (g : (ι → ℝ) → ℂ) (m : ℕ) (l : Fin m → ι) where
  α : Type
  [ft : Fintype α]
  ord : α → ℕ
  dir : (i : α) → Fin (ord i) → ι
  c : α → (ι → ℝ) → ℂ
  ord_le : ∀ i, ord i ≤ m
  smooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i)
  supp : ∀ i (z : ι → ℝ), z ∉ tsupport g → c i =ᶠ[nhds z] 0
  expand : ∀ (v : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) v → ∀ z : ι → ℝ,
      Work.Diff.STE.pdVec m l (fun z => g z * v (T z)) z
        = ∑ i, c i z * Work.Diff.STE.pdVec (ord i) (dir i) v (T z)

attribute [instance] PDExp.ft

/-! ## The induction on the order -/

lemma pdMulComp_exists_expansion (T : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (g : (ι → ℝ) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ∀ (m : ℕ) (l : Fin m → ι), Nonempty (PDExp T g m l) := by
  have hTd : Differentiable ℝ T := hT.differentiable (by simp)
  intro m
  induction m with
  | zero =>
    intro l
    refine ⟨{ α := PUnit, ord := fun _ => 0, dir := fun _ => Fin.elim0, c := fun _ => g,
              ord_le := fun _ => le_rfl,
              smooth := fun _ => hg,
              supp := fun _ z hz => Filter.eventually_of_mem
                ((isClosed_tsupport g).isOpen_compl.mem_nhds hz)
                (fun y hy => image_eq_zero_of_notMem_tsupport hy),
              expand := fun v hv z => by
                simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList] }⟩
  | succ m ih =>
    intro l
    obtain ⟨e⟩ := ih (Fin.tail l)
    -- the coordinate index `ι` is replaced by the equivalent (small) type `Fin (card ι)`, so that
    -- the new index type stays in `Type 0`, as the statement requires.
    let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let ord' : e.α ⊕ (e.α × Fin (Fintype.card ι)) → ℕ := fun i => match i with
      | Sum.inl j => e.ord j
      | Sum.inr jq => e.ord jq.1 + 1
    let dir' : (i : e.α ⊕ (e.α × Fin (Fintype.card ι))) → Fin (ord' i) → ι := fun i => match i with
      | Sum.inl j => e.dir j
      | Sum.inr jq => Fin.cons (eι.symm jq.2) (e.dir jq.1)
    let c' : (e.α ⊕ (e.α × Fin (Fintype.card ι))) → (ι → ℝ) → ℂ := fun i => match i with
      | Sum.inl j => Work.Diff.STE.pd (l 0) (e.c j)
      | Sum.inr jq => fun z => e.c jq.1 z *
          (((fderiv ℝ T z) (Pi.single (l 0) 1)) (eι.symm jq.2) : ℂ)
    refine ⟨PDExp.mk (α := e.α ⊕ (e.α × Fin (Fintype.card ι))) (ord := ord')
      (dir := dir') (c := c') ?_ ?_ ?_ ?_⟩
    · intro i
      cases i with
      | inl j => exact le_trans (e.ord_le j) (Nat.le_succ m)
      | inr jq => exact Nat.succ_le_succ (e.ord_le jq.1)
    · intro i
      cases i with
      | inl j => exact pdMulComp_contDiff_pd (l 0) (e.smooth j)
      | inr jq => exact (e.smooth jq.1).mul (pdMulComp_contDiff_coord_fderiv hT (l 0) (eι.symm jq.2))
    · intro i z hz
      cases i with
      | inl j => exact pdMulComp_pd_eventuallyEq_zero (e.supp j z hz)
      | inr jq =>
        show (e.c jq.1 * fun z =>
            (((fderiv ℝ T z) (Pi.single (l 0) 1)) (eι.symm jq.2) : ℂ)) =ᶠ[nhds z] 0
        simpa using (e.supp jq.1 z hz).mul (Filter.EventuallyEq.refl (nhds z)
          (fun z => (((fderiv ℝ T z) (Pi.single (l 0) 1)) (eι.symm jq.2) : ℂ)))
    · intro v hv z
      have hW : ∀ j : e.α,
          Differentiable ℝ (fun y => Work.Diff.STE.pdVec (e.ord j) (e.dir j) v (T y)) :=
        fun j => ((pdMulComp_contDiff_pdVec (e.ord j) (e.dir j) hv).differentiable (by simp)).comp hTd
      have hc : ∀ j : e.α, Differentiable ℝ (e.c j) :=
        fun j => (e.smooth j).differentiable (by simp)
      have hw : ∀ j : e.α, Differentiable ℝ (Work.Diff.STE.pdVec (e.ord j) (e.dir j) v) :=
        fun j => (pdMulComp_contDiff_pdVec (e.ord j) (e.dir j) hv).differentiable (by simp)
      have hfun : Work.Diff.STE.pdVec m (Fin.tail l) (fun z => g z * v (T z))
          = fun y => ∑ j : e.α, e.c j y * Work.Diff.STE.pdVec (e.ord j) (e.dir j) v (T y) :=
        funext (fun y => e.expand v hv y)
      -- one step of `pd`, the finite sum and the Leibniz rule
      have hstep1 : Work.Diff.STE.pdVec (m + 1) l (fun z => g z * v (T z)) z
          = ∑ j : e.α, (e.c j z
              * Work.Diff.STE.pd (l 0) (fun y => Work.Diff.STE.pdVec (e.ord j) (e.dir j) v (T y)) z
              + Work.Diff.STE.pdVec (e.ord j) (e.dir j) v (T z)
                * Work.Diff.STE.pd (l 0) (e.c j) z) := by
        rw [pdMulComp_pdVec_succ_cons m l, hfun,
          pdMulComp_pd_sum (l 0)
            (fun j : e.α => fun y => e.c j y * Work.Diff.STE.pdVec (e.ord j) (e.dir j) v (T y))
            (fun j => (hc j).mul (hW j)) z]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        show Work.Diff.STE.pd (l 0)
            (e.c j * fun y => Work.Diff.STE.pdVec (e.ord j) (e.dir j) v (T y)) z
          = e.c j z
              * Work.Diff.STE.pd (l 0) (fun y => Work.Diff.STE.pdVec (e.ord j) (e.dir j) v (T y)) z
            + Work.Diff.STE.pdVec (e.ord j) (e.dir j) v (T z)
              * Work.Diff.STE.pd (l 0) (e.c j) z
        rw [pdMulComp_pd_mul (l 0) (e.c j)
          (fun y => Work.Diff.STE.pdVec (e.ord j) (e.dir j) v (T y)) (hc j) (hW j)]
        rfl
      -- the chain rule for the transported derivative of `v`
      have hstep2 : ∀ j : e.α,
          Work.Diff.STE.pd (l 0) (fun y => Work.Diff.STE.pdVec (e.ord j) (e.dir j) v (T y)) z
          = ∑ p : ι, (((fderiv ℝ T z) (Pi.single (l 0) 1)) p : ℂ)
              * Work.Diff.STE.pdVec (e.ord j + 1) (Fin.cons p (e.dir j)) v (T z) := by
        intro j
        rw [pdMulComp_pd_comp_eq hTd (l 0) (hw j)]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [pdMulComp_pd_pdVec_cons]
      -- identification of the two families of terms with the two summands of the new index type
      have hB : (∑ j : e.α, Work.Diff.STE.pdVec (e.ord j) (e.dir j) v (T z)
              * Work.Diff.STE.pd (l 0) (e.c j) z)
          = ∑ j : e.α, c' (Sum.inl j) z
              * Work.Diff.STE.pdVec (ord' (Sum.inl j)) (dir' (Sum.inl j)) v (T z) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        dsimp only [c', ord', dir']
        ring
      have hA : (∑ j : e.α, e.c j z * (∑ p : ι, (((fderiv ℝ T z) (Pi.single (l 0) 1)) p : ℂ)
              * Work.Diff.STE.pdVec (e.ord j + 1) (Fin.cons p (e.dir j)) v (T z)))
          = ∑ jq : e.α × Fin (Fintype.card ι), c' (Sum.inr jq) z
              * Work.Diff.STE.pdVec (ord' (Sum.inr jq)) (dir' (Sum.inr jq)) v (T z) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← Equiv.sum_comp eι.symm (fun p : ι =>
          (((fderiv ℝ T z) (Pi.single (l 0) 1)) p : ℂ)
            * Work.Diff.STE.pdVec (e.ord j + 1) (Fin.cons p (e.dir j)) v (T z))]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        dsimp only [c', ord', dir']
        ring
      have hsplit : (∑ i : e.α ⊕ (e.α × Fin (Fintype.card ι)), c' i z
            * Work.Diff.STE.pdVec (ord' i) (dir' i) v (T z))
          = (∑ j : e.α, c' (Sum.inl j) z
                * Work.Diff.STE.pdVec (ord' (Sum.inl j)) (dir' (Sum.inl j)) v (T z))
            + (∑ jq : e.α × Fin (Fintype.card ι), c' (Sum.inr jq) z
                * Work.Diff.STE.pdVec (ord' (Sum.inr jq)) (dir' (Sum.inr jq)) v (T z)) :=
        Fintype.sum_sum_type _
      rw [hstep1, Finset.sum_add_distrib, add_comm]
      simp only [hstep2]
      rw [hsplit, ← hB, ← hA]

/-- **The requested expansion of the iterated derivatives of `g · (v ∘ T)`.** -/
theorem pdVecMulCompExpansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (g : (ι → ℝ) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (m : ℕ) (l : Fin m → ι) :
    ∃ (α : Type) (_ : Fintype α) (ord : α → ℕ) (dir : (i : α) → Fin (ord i) → ι)
      (c : α → (ι → ℝ) → ℂ),
      (∀ i, ord i ≤ m) ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i)) ∧
      (∀ i (z : ι → ℝ), z ∉ tsupport g → c i z = 0) ∧
      (∀ (v : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) v → ∀ z : ι → ℝ,
        Work.Diff.STE.pdVec m l (fun z => g z * v (T z)) z
          = ∑ i, c i z * Work.Diff.STE.pdVec (ord i) (dir i) v (T z)) := by
  obtain ⟨e⟩ := pdMulComp_exists_expansion T hT g hg m l
  exact ⟨e.α, e.ft, e.ord, e.dir, e.c, e.ord_le, e.smooth,
    (fun i z hz => (e.supp i z hz).eq_of_nhds), e.expand⟩

end Work.Diff.STE.B3
