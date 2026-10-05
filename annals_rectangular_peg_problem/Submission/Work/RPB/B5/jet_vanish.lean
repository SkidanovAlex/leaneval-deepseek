import Mathlib

/-!
# Vanishing of the jets of a function flat in the normal direction

`Work.RPB.B5.jet_vanish`: if `G : P × ℝ → E` is `C^k` on `A × [0,∞)`, vanishes on `A × {0}`, and
all one-sided `σ`-derivatives of the slices `σ ↦ G (p, σ)` vanish at `0` up to order `k`, then the
Fréchet derivatives of `G` of order `≤ k` at `(p, 0)`, taken within `A × [0,∞)`, vanish.

The proof is an induction on the order `m` of the derivative, writing the `m`-th derivative as an
iterated one-sided directional derivative in the variables of `P × ℝ` (the auxiliary `Dfun`,
`Diter` below).  Splitting the outermost direction into its `P`- and `σ`-components,

* the `P`-component only sees the restriction of the inner function to the base `A × {0}`, where
  it vanishes by the induction hypothesis (this is `Dfun_free_eq`);
* the `σ`-component can be moved through the remaining directional derivatives to the innermost
  position (this is `Diter_eσ_commute`), so that the induction hypothesis applies to the function
  `∂_σ G`, whose slices are again flat (one order lower).

All the auxiliary material is `private` to this file; a public parallel copy lives in
`Submission/Work/RPB/B5/contDiffOn_flat_trunc.lean`.
-/

open scoped ContDiff Topology

open Filter Set

namespace Work.RPB.B5

set_option autoImplicit false

noncomputable section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Iterated one-sided directional derivatives -/

/-- The one-sided directional derivative of `g` in direction `v`, along the set `s`. -/
private noncomputable def Dfun {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] (s : Set E') (v : E') (g : E' → F) : E' → F :=
  fun y => fderivWithin ℝ g s y v

/-- The `n`-fold iterated one-sided directional derivative in the directions `v`. -/
private noncomputable def Diter {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] (s : Set E') (f : E' → F) :
    (n : ℕ) → (Fin n → E') → E' → F
  | 0, _ => f
  | n+1, v => Dfun s (v 0) (Diter s f n (Fin.tail v))

/-- `Dfun` is additive in the direction. -/
private theorem Dfun_add {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] (s : Set E') (v w : E') (g : E' → F) (y : E') :
    Dfun s (v + w) g y = Dfun s v g y + Dfun s w g y := by
  simp only [Dfun]
  rw [map_add]

/-- `Dfun` is homogeneous in the direction. -/
private theorem Dfun_smul {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] (s : Set E') (c : ℝ) (v : E') (g : E' → F)
    (y : E') : Dfun s (c • v) g y = c • Dfun s v g y := by
  simp only [Dfun]
  rw [map_smul]

/-- **Second-derivative symmetry** for the one-sided directional derivative. -/
private theorem Dfun_comm {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E'} {g : E' → F} {x a b : E'}
    (hs : UniqueDiffOn ℝ s) (hxs : x ∈ s) (hxci : x ∈ closure (interior s))
    (hg : ContDiffOn ℝ (2 : WithTop ℕ∞) g s) :
    Dfun s a (Dfun s b g) x = Dfun s b (Dfun s a g) x := by
  have hsx : UniqueDiffWithinAt ℝ s x := hs x hxs
  have hsymm := (hg.contDiffWithinAt hxs).isSymmSndFDerivWithinAt (𝕜 := ℝ) (by norm_num) hs hxci hxs
  have hdiff : DifferentiableWithinAt ℝ (fun y => fderivWithin ℝ g s y) s x := by
    have h1 : ContDiffOn ℝ (1 : WithTop ℕ∞) (fderivWithin ℝ g s) s := by
      have := (contDiffOn_succ_iff_fderivWithin (𝕜 := ℝ) (f := g) (n := (1 : WithTop ℕ∞))
        hs).mp hg
      simpa using this.2.2
    exact (h1.differentiableOn (by norm_num)) x hxs
  have e1 : fderivWithin ℝ (fun y => fderivWithin ℝ g s y b) s x a
      = ((fderivWithin ℝ (fun y => fderivWithin ℝ g s y) s x).flip b) a := by
    rw [fderivWithin_clm_apply hsx hdiff (differentiableWithinAt_const b)]
    simp [ContinuousLinearMap.flip_apply]
  have e2 : fderivWithin ℝ (fun y => fderivWithin ℝ g s y a) s x b
      = ((fderivWithin ℝ (fun y => fderivWithin ℝ g s y) s x).flip a) b := by
    rw [fderivWithin_clm_apply hsx hdiff (differentiableWithinAt_const a)]
    simp [ContinuousLinearMap.flip_apply]
  have e3 : fderivWithin ℝ (fun y => fderivWithin ℝ g s y) s x a b
      = ((fderivWithin ℝ (fun y => fderivWithin ℝ g s y) s x).flip b) a := by
    simp [ContinuousLinearMap.flip_apply]
  have e4 : fderivWithin ℝ (fun y => fderivWithin ℝ g s y) s x b a
      = ((fderivWithin ℝ (fun y => fderivWithin ℝ g s y) s x).flip a) b := by
    simp [ContinuousLinearMap.flip_apply]
  rw [show Dfun s a (Dfun s b g) x
        = fderivWithin ℝ (fun y => fderivWithin ℝ g s y b) s x a from rfl,
      show Dfun s b (Dfun s a g) x
        = fderivWithin ℝ (fun y => fderivWithin ℝ g s y a) s x b from rfl]
  rw [e1, e2, ← e3, ← e4]
  exact hsymm a b

/-- **The iterated Fréchet derivative within a set is the iterated one-sided directional
derivative.** -/
private theorem iteratedFDerivWithin_eq_Diter {E' F : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) :
    ∀ (f : E' → F) (s : Set E'), UniqueDiffOn ℝ s → ContDiffOn ℝ (n : WithTop ℕ∞) f s →
      ∀ x ∈ s, ∀ v : Fin n → E', (iteratedFDerivWithin ℝ n f s x) v = Diter s f n v x := by
  induction n with
  | zero => intro f s hs hf x hx v; simp [iteratedFDerivWithin_zero_apply, Diter]
  | succ n ih =>
    intro f s hs hf x hx v
    have hfn : ContDiffOn ℝ (n : WithTop ℕ∞) f s := hf.of_le (by exact_mod_cast Nat.le_succ n)
    have hdiff : DifferentiableWithinAt ℝ (iteratedFDerivWithin ℝ n f s) s x :=
      (hf.differentiableOn_iteratedFDerivWithin (m := n)
        (by exact_mod_cast Nat.lt_succ_self n) hs) x hx
    rw [iteratedFDerivWithin_succ_apply_left]
    have hstep : ((fderivWithin ℝ (iteratedFDerivWithin ℝ n f s) s x) (v 0)) (Fin.tail v)
        = fderivWithin ℝ (fun y => (iteratedFDerivWithin ℝ n f s y) (Fin.tail v)) s x (v 0) := by
      rw [fderivWithin_continuousMultilinear_apply_const (hs x hx) hdiff (Fin.tail v)]
      rfl
    rw [hstep]
    have hcongr : fderivWithin ℝ (fun y => (iteratedFDerivWithin ℝ n f s y) (Fin.tail v)) s x
        = fderivWithin ℝ (Diter s f n (Fin.tail v)) s x := by
      refine fderivWithin_congr (fun y hy => ?_) (ih f s hs hfn x hx (Fin.tail v))
      exact ih f s hs hfn y hy (Fin.tail v)
    rw [hcongr]
    simp only [Diter]
    rfl

/-- `Diter` preserves smoothness. -/
private theorem Diter_contDiffOn {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] (s : Set E') (hs : UniqueDiffOn ℝ s) :
    ∀ (n j : ℕ) (f : E' → F), ContDiffOn ℝ ((j + n : ℕ) : WithTop ℕ∞) f s →
      ∀ v : Fin n → E', ContDiffOn ℝ (j : WithTop ℕ∞) (Diter s f n v) s := by
  intro n
  induction n with
  | zero => intro j f hf v; simpa [Diter] using hf
  | succ n ih =>
    intro j f hf v
    have hfj : ContDiffOn ℝ (((j + 1) + n : ℕ) : WithTop ℕ∞) f s := by
      rw [show (j + (n + 1) : ℕ) = ((j + 1) + n) from by omega] at hf
      exact hf
    have ihv : ContDiffOn ℝ ((j : WithTop ℕ∞))
        (fderivWithin ℝ (Diter s f n (Fin.tail v)) s) s :=
      (ih (j + 1) f hfj (Fin.tail v)).fderivWithin hs (m := (j : WithTop ℕ∞))
        (by rw [Nat.cast_add, Nat.cast_one])
    change ContDiffOn ℝ ((j : WithTop ℕ∞))
      (fun y => (fderivWithin ℝ (Diter s f n (Fin.tail v)) s y) (v 0)) s
    exact ihv.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ F (v 0))

/-- The "free" directional derivative at a seam point is the `fderivWithin` on the base `A`. -/
private theorem Dfun_free_eq (A : Set P) (u : P) (H : P × ℝ → E) (p : P)
    (hA : UniqueDiffWithinAt ℝ A p)
    (hH : DifferentiableWithinAt ℝ H (A ×ˢ Set.Ici (0:ℝ)) (p, 0)) :
    Dfun (A ×ˢ Set.Ici (0:ℝ)) (u, (0 : ℝ)) H (p, 0)
      = fderivWithin ℝ (fun q => H (q, (0 : ℝ))) A p u := by
  have hγ : HasFDerivWithinAt (fun q : P => (q, (0 : ℝ))) (ContinuousLinearMap.inl ℝ P ℝ) A p :=
    (ContinuousLinearMap.inl ℝ P ℝ).hasFDerivWithinAt
  have hmaps : Set.MapsTo (fun q : P => (q, (0 : ℝ))) A (A ×ˢ Set.Ici (0:ℝ)) :=
    fun q hq => ⟨hq, le_refl (0 : ℝ)⟩
  have hcomp := HasFDerivWithinAt.comp p hH.hasFDerivWithinAt hγ hmaps
  have hfd : fderivWithin ℝ (fun q : P => H (q, (0 : ℝ))) A p
      = (fderivWithin ℝ H (A ×ˢ Set.Ici (0:ℝ)) (p, 0)) ∘SL (ContinuousLinearMap.inl ℝ P ℝ) := by
    simpa only [Function.comp_def] using hcomp.fderivWithin hA
  rw [Dfun]
  change (fderivWithin ℝ H (A ×ˢ Set.Ici (0:ℝ)) (p, 0)) (u, (0 : ℝ)) = _
  rw [hfd]
  simp [ContinuousLinearMap.comp_apply]

/-- Moving a normal (`σ`-) derivative through the iterated directional derivatives. -/
private theorem Diter_eσ_commute (A : Set P) (hA : UniqueDiffOn ℝ A)
    (hAcl : ∀ p ∈ A, p ∈ closure (interior A)) (G : P × ℝ → E) :
    ∀ (n : ℕ), ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) G (A ×ˢ Set.Ici (0:ℝ)) →
      ∀ v : Fin n → (P × ℝ), ∀ y ∈ (A ×ˢ Set.Ici (0:ℝ)),
        Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ))
            (Diter (A ×ˢ Set.Ici (0:ℝ)) G n v) y
          = Diter (A ×ˢ Set.Ici (0:ℝ))
              (Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G) n v y := by
  intro n
  induction n with
  | zero =>
    intro hG v y hy
    simp only [Diter]
  | succ n ih =>
    intro hG v y hy
    have hGn : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) G (A ×ˢ Set.Ici (0:ℝ)) :=
      hG.of_le (by exact_mod_cast Nat.le_succ (n + 1))
    have hSn : ContDiffOn ℝ (2 : WithTop ℕ∞)
        (Diter (A ×ˢ Set.Ici (0:ℝ)) G n (Fin.tail v)) (A ×ˢ Set.Ici (0:ℝ)) :=
      Diter_contDiffOn (A ×ˢ Set.Ici (0:ℝ)) (hA.prod (uniqueDiffOn_Ici 0)) n 2 G
        (hG.of_le (le_of_eq (by push_cast; ring))) (Fin.tail v)
    have hSud : UniqueDiffOn ℝ (A ×ˢ Set.Ici (0:ℝ)) := hA.prod (uniqueDiffOn_Ici 0)
    have hycl : y ∈ closure (interior (A ×ˢ Set.Ici (0:ℝ))) := by
      rcases y with ⟨p, σ⟩
      simp only [Set.mem_prod] at hy
      rw [interior_prod_eq, interior_Ici, closure_prod_eq, closure_Ioi, Set.mem_prod]
      exact ⟨hAcl p hy.1, hy.2⟩
    rw [show Diter (A ×ˢ Set.Ici (0:ℝ)) G (n + 1) v
        = Dfun (A ×ˢ Set.Ici (0:ℝ)) (v 0)
            (Diter (A ×ˢ Set.Ici (0:ℝ)) G n (Fin.tail v)) from rfl]
    rw [Dfun_comm hSud hy hycl hSn]
    have heq : ∀ z ∈ (A ×ˢ Set.Ici (0:ℝ)),
        Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ))
            (Diter (A ×ˢ Set.Ici (0:ℝ)) G n (Fin.tail v)) z
          = Diter (A ×ˢ Set.Ici (0:ℝ))
              (Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G) n (Fin.tail v) z :=
      fun z hz => ih hGn (Fin.tail v) z hz
    change (fderivWithin ℝ
            (Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ))
              (Diter (A ×ˢ Set.Ici (0:ℝ)) G n (Fin.tail v))) (A ×ˢ Set.Ici (0:ℝ)) y) (v 0)
        = (fderivWithin ℝ
            (Diter (A ×ˢ Set.Ici (0:ℝ))
              (Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G) n (Fin.tail v))
            (A ×ˢ Set.Ici (0:ℝ)) y) (v 0)
    rw [fderivWithin_congr heq (heq y hy)]

/-! ## The `σ`-derivative of `G` at the seam -/

/-- For `σ > 0`, the within-`S` derivative of `G` at `(p, σ)` in the direction `(0, 1)` is the
derivative of the slice `t ↦ G (p, t)`. -/
private theorem Dfun_e_eq_deriv {k : ℕ} (hk : 1 ≤ k) (A : Set P) (G : P × ℝ → E)
    (hG : ContDiffOn ℝ (k : WithTop ℕ∞) G (A ×ˢ Set.Ici (0:ℝ)))
    {p : P} (hp : p ∈ A) {σ : ℝ} (hσ : 0 < σ) :
    Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G (p, σ)
      = deriv (fun t : ℝ => G (p, t)) σ := by
  have hne : (k : WithTop ℕ∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hGdiff : DifferentiableWithinAt ℝ G (A ×ˢ Set.Ici (0:ℝ)) (p, σ) :=
    (hG.differentiableOn hne) (p, σ) ⟨hp, Set.mem_Ici.mpr (le_of_lt hσ)⟩
  have hγ : HasDerivWithinAt (fun t : ℝ => (p, t)) ((0:P), (1:ℝ)) (Set.Ioi (0:ℝ)) σ :=
    ((hasDerivAt_const σ p).prodMk (hasDerivAt_id σ)).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun t : ℝ => (p, t)) (Set.Ioi (0:ℝ)) (A ×ˢ Set.Ici (0:ℝ)) :=
    fun t ht => ⟨hp, Set.mem_Ici.mpr (le_of_lt ht)⟩
  have hchain := hGdiff.hasFDerivWithinAt.comp_hasDerivWithinAt σ hγ hmaps
  have hderiv := hchain.hasDerivAt (isOpen_Ioi.mem_nhds hσ)
  rw [Dfun, ← hderiv.deriv]
  rfl

/-- The within-`S` derivative of `G` at `(p, 0)` in the direction `(0, 1)` vanishes. -/
private theorem Dfun_e_eq_zero {k : ℕ} (hk : 1 ≤ k) (A : Set P) (G : P × ℝ → E)
    (hG : ContDiffOn ℝ (k : WithTop ℕ∞) G (A ×ˢ Set.Ici (0:ℝ)))
    (hflat : ∀ p ∈ A, ∀ j : ℕ, j ≤ k →
      iteratedDerivWithin j (fun σ : ℝ => G (p, σ)) (Set.Ioi (0:ℝ)) 0 = 0) :
    ∀ p ∈ A, Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G (p, 0) = 0 := by
  intro p hp
  have hne : (k : WithTop ℕ∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hGdiff : DifferentiableWithinAt ℝ G (A ×ˢ Set.Ici (0:ℝ)) (p, 0) :=
    (hG.differentiableOn hne) (p, 0) ⟨hp, Set.mem_Ici.mpr (le_refl 0)⟩
  have hγ : HasDerivWithinAt (fun t : ℝ => (p, t)) ((0:P), (1:ℝ)) (Set.Ioi (0:ℝ)) 0 :=
    ((hasDerivAt_const (0:ℝ) p).prodMk (hasDerivAt_id (0:ℝ))).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun t : ℝ => (p, t)) (Set.Ioi (0:ℝ)) (A ×ˢ Set.Ici (0:ℝ)) :=
    fun t ht => ⟨hp, Set.mem_Ici.mpr (le_of_lt ht)⟩
  have hchain := hGdiff.hasFDerivWithinAt.comp_hasDerivWithinAt 0 hγ hmaps
  have h1 : derivWithin (fun t : ℝ => G (p, t)) (Set.Ioi (0:ℝ)) 0
      = (fderivWithin ℝ G (A ×ˢ Set.Ici (0:ℝ)) (p, 0)) ((0:P), (1:ℝ)) :=
    hchain.derivWithin (uniqueDiffWithinAt_Ioi 0)
  rw [Dfun, ← h1, ← iteratedDerivWithin_one]
  exact hflat p hp 1 hk

/-! ## Hypothesis transfer to the `σ`-derivative -/

/-- The `σ`-derivative of a `C^k` function on `A × [0, ∞)` is `C^{k-1}` there. -/
private theorem contDiffOn_Dfun_e {k : ℕ} (hk : 1 ≤ k) (A : Set P) (hA : UniqueDiffOn ℝ A)
    (G : P × ℝ → E) (hG : ContDiffOn ℝ (k : WithTop ℕ∞) G (A ×ˢ Set.Ici (0:ℝ))) :
    ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
      (Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G) (A ×ˢ Set.Ici (0:ℝ)) := by
  have hS : UniqueDiffOn ℝ (A ×ˢ Set.Ici (0:ℝ)) := hA.prod (uniqueDiffOn_Ici 0)
  have hmn : ((k - 1 : ℕ) : WithTop ℕ∞) + 1 ≤ (k : WithTop ℕ∞) := by
    have h : k - 1 + 1 = k := Nat.sub_add_cancel hk
    rw [← h]
    push_cast
    rfl
  have hfd := hG.fderivWithin hS hmn
  have hcomp := hfd.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ E ((0:P), (1:ℝ)))
  exact hcomp

/-- The slices of the `σ`-derivative of `G` are flat of order `k - 1`. -/
private theorem flat_Dfun_e {k : ℕ} (hk : 1 ≤ k) (A : Set P) (G : P × ℝ → E)
    (hG : ContDiffOn ℝ (k : WithTop ℕ∞) G (A ×ˢ Set.Ici (0:ℝ)))
    (hflat : ∀ p ∈ A, ∀ j : ℕ, j ≤ k →
      iteratedDerivWithin j (fun σ : ℝ => G (p, σ)) (Set.Ioi (0:ℝ)) 0 = 0) :
    ∀ p ∈ A, ∀ j : ℕ, j ≤ k - 1 →
      iteratedDerivWithin j
        (fun σ : ℝ => Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G (p, σ))
        (Set.Ioi (0:ℝ)) 0 = 0 := by
  intro p hp j hj
  have hEqOn : Set.EqOn
      (fun σ : ℝ => Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G (p, σ))
      (fun σ : ℝ => derivWithin (fun t : ℝ => G (p, t)) (Set.Ioi (0:ℝ)) σ) (Set.Ioi (0:ℝ)) := by
    intro σ hσ
    show Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G (p, σ)
        = derivWithin (fun t : ℝ => G (p, t)) (Set.Ioi (0:ℝ)) σ
    rw [Dfun_e_eq_deriv hk A G hG hp hσ]
    exact (derivWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hσ)).symm
  have hev : (fun σ : ℝ => Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G (p, σ))
      =ᶠ[𝓝[Set.Ioi (0:ℝ)] 0]
      (fun σ : ℝ => derivWithin (fun t : ℝ => G (p, t)) (Set.Ioi (0:ℝ)) σ) :=
    hEqOn.eventuallyEq_nhdsWithin
  have hval : (fun σ : ℝ => Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G (p, σ)) 0
      = (fun σ : ℝ => derivWithin (fun t : ℝ => G (p, t)) (Set.Ioi (0:ℝ)) σ) 0 := by
    simp only
    rw [Dfun_e_eq_zero hk A G hG hflat p hp, ← iteratedDerivWithin_one]
    exact (hflat p hp 1 hk).symm
  rw [Filter.EventuallyEq.iteratedDerivWithin_eq hev hval, ← iteratedDerivWithin_succ']
  exact hflat p hp (j + 1) (by omega)

/-! ## The main induction -/

/-- Auxiliary induction statement for `jet_vanish`. -/
private theorem jet_aux (A : Set P) (hA : UniqueDiffOn ℝ A)
    (hAcl : ∀ p ∈ A, p ∈ closure (interior A)) (m : ℕ) :
    ∀ k : ℕ, m ≤ k → ∀ G : P × ℝ → E,
      ContDiffOn ℝ (k : WithTop ℕ∞) G (A ×ˢ Set.Ici (0:ℝ)) →
      (∀ p ∈ A, G (p, 0) = 0) →
      (∀ p ∈ A, ∀ j : ℕ, j ≤ k →
        iteratedDerivWithin j (fun σ : ℝ => G (p, σ)) (Set.Ioi (0:ℝ)) 0 = 0) →
      ∀ p ∈ A, iteratedFDerivWithin ℝ m G (A ×ˢ Set.Ici (0:ℝ)) (p, 0) = 0 := by
  induction m with
  | zero =>
    intro k _ G _ h0 _ p hp
    ext v
    rw [iteratedFDerivWithin_zero_apply]
    simpa using h0 p hp
  | succ m ih =>
    intro k hmk G hG h0 hflat p hp
    have hk1 : 1 ≤ k := by omega
    have hmk' : m ≤ k := by omega
    have hS : UniqueDiffOn ℝ (A ×ˢ Set.Ici (0:ℝ)) := hA.prod (uniqueDiffOn_Ici 0)
    have hmem : (p, (0:ℝ)) ∈ A ×ˢ Set.Ici (0:ℝ) := ⟨hp, Set.mem_Ici.mpr (le_refl 0)⟩
    have hGm1 : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) G (A ×ˢ Set.Ici (0:ℝ)) :=
      hG.of_le (by exact_mod_cast hmk)
    have hGm : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) G (A ×ˢ Set.Ici (0:ℝ)) :=
      hG.of_le (by exact_mod_cast hmk')
    ext v
    rw [iteratedFDerivWithin_eq_Diter (m+1) G (A ×ˢ Set.Ici (0:ℝ)) hS hGm1 (p, 0) hmem v]
    set H : P × ℝ → E := Diter (A ×ˢ Set.Ici (0:ℝ)) G m (Fin.tail v) with hHdef
    have hsplit : Dfun (A ×ˢ Set.Ici (0:ℝ)) (v 0) H (p, 0)
        = Dfun (A ×ˢ Set.Ici (0:ℝ)) ((v 0).1, (0:ℝ)) H (p, 0)
          + (v 0).2 • Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) H (p, 0) := by
      conv_lhs => rw [show (v 0 : P × ℝ) = ((v 0).1, (0:ℝ)) + (v 0).2 • ((0:P), (1:ℝ))
                            from by ext <;> simp]
      rw [Dfun_add, Dfun_smul]
    have hHdiff : DifferentiableWithinAt ℝ H (A ×ˢ Set.Ici (0:ℝ)) (p, 0) := by
      have hC1 : ContDiffOn ℝ (1 : WithTop ℕ∞) H (A ×ˢ Set.Ici (0:ℝ)) := by
        rw [hHdef]
        exact Diter_contDiffOn (A ×ˢ Set.Ici (0:ℝ)) hS m 1 G
          (hG.of_le (by exact_mod_cast (show 1 + m ≤ k by omega))) (Fin.tail v)
      exact (hC1.differentiableOn (by norm_num)) (p, 0) hmem
    have hH0 : ∀ q ∈ A, H (q, (0:ℝ)) = 0 := by
      intro q hq
      have hqmem : (q, (0:ℝ)) ∈ A ×ˢ Set.Ici (0:ℝ) := ⟨hq, Set.mem_Ici.mpr (le_refl 0)⟩
      rw [hHdef]
      rw [← iteratedFDerivWithin_eq_Diter m G (A ×ˢ Set.Ici (0:ℝ)) hS hGm (q, 0) hqmem
            (Fin.tail v)]
      rw [ih k hmk' G hG h0 hflat q hq]
      simp
    have hG'e : ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞)
        (Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G) (A ×ˢ Set.Ici (0:ℝ)) :=
      contDiffOn_Dfun_e hk1 A hA G hG
    have hG'0 : ∀ q ∈ A, Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G (q, 0) = 0 :=
      Dfun_e_eq_zero hk1 A G hG hflat
    have hG'flat : ∀ q ∈ A, ∀ j : ℕ, j ≤ k - 1 →
        iteratedDerivWithin j
          (fun σ : ℝ => Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G (q, σ))
          (Set.Ioi (0:ℝ)) 0 = 0 :=
      flat_Dfun_e hk1 A G hG hflat
    have hG'em : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞)
        (Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G) (A ×ˢ Set.Ici (0:ℝ)) :=
      hG'e.of_le (by exact_mod_cast (show m ≤ k - 1 by omega))
    have hterm1 : Dfun (A ×ˢ Set.Ici (0:ℝ)) ((v 0).1, (0:ℝ)) H (p, 0) = 0 := by
      rw [Dfun_free_eq A (v 0).1 H p (hA p hp) hHdiff]
      rw [fderivWithin_congr (f₁ := fun q => H (q, (0:ℝ)))
            (f := Function.const P (0 : E)) (fun q hq => hH0 q hq) (hH0 p hp)]
      simp
    have hterm2 : Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) H (p, 0) = 0 := by
      rw [hHdef]
      rw [Diter_eσ_commute A hA hAcl G m hGm1 (Fin.tail v) (p, 0) hmem]
      rw [← iteratedFDerivWithin_eq_Diter m (Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G)
            (A ×ˢ Set.Ici (0:ℝ)) hS hG'em (p, 0) hmem (Fin.tail v)]
      rw [ih (k - 1) (by omega) (Dfun (A ×ˢ Set.Ici (0:ℝ)) ((0:P), (1:ℝ)) G) hG'e hG'0
            hG'flat p hp]
      simp
    change Dfun (A ×ˢ Set.Ici (0:ℝ)) (v 0) H (p, 0) = 0
    rw [hsplit, hterm1, hterm2, zero_add, smul_zero]

/-! ## The main theorem -/

theorem jet_vanish {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (A : Set P)
    (hA : UniqueDiffOn ℝ A) (hAcl : ∀ p ∈ A, p ∈ closure (interior A)) (k : ℕ) (G : P × ℝ → E)
    (hG : ContDiffOn ℝ (k : WithTop ℕ∞) G (A ×ˢ Set.Ici (0:ℝ)))
    (h0 : ∀ p ∈ A, G (p, 0) = 0)
    (hflat : ∀ p ∈ A, ∀ j : ℕ, j ≤ k →
      iteratedDerivWithin j (fun σ : ℝ => G (p, σ)) (Set.Ioi (0:ℝ)) 0 = 0) :
    ∀ m ≤ k, ∀ p ∈ A,
      iteratedFDerivWithin ℝ m G (A ×ˢ Set.Ici (0:ℝ)) (p, 0) = 0 := by
  intro m hmk
  exact jet_aux A hA hAcl m k hmk G hG h0 hflat

end

end Work.RPB.B5
