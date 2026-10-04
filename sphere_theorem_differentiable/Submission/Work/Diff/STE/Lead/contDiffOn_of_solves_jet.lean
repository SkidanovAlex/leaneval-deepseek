import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.Lead.Defs
import Submission.Work.Diff.STE.Lead.contDiffOn_succ_of_partial_of_hasFDeriv
import Submission.Work.Diff.STE.Lead.pdW_comp_jet
import Submission.Work.Diff.STE.Lead.pdW_commute_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bootstrap: a solution of `∂ₜ V = Φ (·, jet V)` with smooth slices and a continuous jet
tower is jointly `C^∞`

The target `Work.Diff.STE.Lead.contDiffOn_of_solves_jet` is the last layer of the flat analytic
core of short-time existence for the DeTurck system: the limit produced by the compactness
argument is only known to be (a) `C^∞` in the space variable for each time, (b) *jointly
continuous with all its spatial derivatives* (this is what the uniform `H^k` bounds give) and
(c) to solve the (closed, quasilinear) PDE pointwise in time.  The lemma below upgrades these
three facts to joint `C^∞`.

## Plan of the proof

Write `W (t,y) = V t y` and `G (t,y) = Φ (y, jetM (V t) y)`, so that `∂ₜ W = G` holds
one-sidedly on `Ico 0 τ`.  The invariant of the induction is (for `m : ℕ`)

  `M(m)`:  for every entry `(a,b)` and every word `β`, the spatial derivative `∂_β W_{ab}` is
           `C^m` on `Ico 0 τ ×ˢ Ω`.

* `M 0` is exactly the hypothesis `hjet` on the jet tower (`continuousOn_pdW`).
* `M m → M (m+1)`: for a word `β` and an entry `(a,b)` we need `∂ₜ (∂_β W_{ab})` and
  `∂_c (∂_β W_{ab})` to be `C^m`:
  - the spatial derivative is `∂_{c :: β} W_{ab}`, which is `C^m` by `M m`;
  - the time derivative is `∂_β G_{ab}` (the `t`-`y` commutation: `pdW_commute`), and
    `∂_β G_{ab}` is a *smooth function of the jet tower* (jet chain rule `pdW_comp_jet`);
    evaluated on the tower entries — which are `C^m` by `M m` — this is `C^m`.
  The two partial derivatives of `∂_β W_{ab}` are therefore `C^m`, so `∂_β W_{ab} ∈ C^{m+1}`
  by the two-variable criterion `contDiffOn_succ_of_partial_of_hasFDeriv`.

## Pieces (delegated, in `Submission/Work/Diff/STE/Lead/`)

* `pdW_comp_jet` (`pdW_comp_jet.lean`): the jet chain rule — the `β`-th spatial derivative of
  `Φ (·, jetM u)` is a smooth function `Ψ` of the `(|β|+2)`-jet of `u`; this is what makes
  `∂_β G` computable from the tower.
* `contDiffOn_succ_of_partial_of_hasFDeriv` (`contDiffOn_succ_of_partial_of_hasFDeriv.lean`):
  the two-variable criterion (a function whose two partial derivatives exist and are `C^m` is
  `C^(m+1)`, also on a half-open slab and at the boundary point `t = 0`).
* `pdW_commute` (`pdW_commute.lean`): the `t`-`y` commutation, from the integral form of the
  equation.

The vocabulary (`pdW`, `compTower`, `Idx`, ...) is in `Defs.lean`; the linear algebra of the
coordinate frame (`bLin`, `fderiv_pdW`, ...) and the jet-tower smoothness of a single slice are
proved in this file.
-/

open scoped ContDiff BigOperators
open Set Filter

namespace Work.Diff.STE.Lead

variable {n : ℕ}

/-! ## The objects of the bootstrap -/

/-- The right hand side `G (t,y) = Φ (y, jetM (V t) y)` of the equation. -/
noncomputable def Gterm (Φ : Modl n × Work.Diff.STE.Flat.Jet n → Mtrx n)
    (V : ℝ → Modl n → Mtrx n) : ℝ × Modl n → Mtrx n :=
  fun p => Φ (p.2, Work.Diff.STE.Flat.jetM (V p.1) p.2)

/-- The slice at time `t` of the right hand side. -/
noncomputable def Gslice (Φ : Modl n × Work.Diff.STE.Flat.Jet n → Mtrx n)
    (V : ℝ → Modl n → Mtrx n) (t : ℝ) : Modl n → Mtrx n :=
  fun y => Φ (y, Work.Diff.STE.Flat.jetM (V t) y)

@[simp] lemma Gterm_apply (Φ : Modl n × Work.Diff.STE.Flat.Jet n → Mtrx n)
    (V : ℝ → Modl n → Mtrx n) (p : ℝ × Modl n) : Gterm Φ V p = Gslice Φ V p.1 p.2 := rfl

/-- The `j`-th spatial derivative (along the word `w`) of the `(a,b)`-entry of `V`. -/
noncomputable def xi (V : ℝ → Modl n → Mtrx n) (j : ℕ) (w : Fin j → Fin n) (a b : Fin n) :
    ℝ × Modl n → ℂ :=
  fun p => pdW (fun y' => V p.1 y' a b) j w p.2

/-- The `j`-th spatial derivative (along the word `w`) of the `(a,b)`-entry of `G`. -/
noncomputable def zeta (Φ : Modl n × Work.Diff.STE.Flat.Jet n → Mtrx n)
    (V : ℝ → Modl n → Mtrx n) (j : ℕ) (w : Fin j → Fin n) (a b : Fin n) : ℝ × Modl n → ℂ :=
  fun p => pdW (fun y' => Φ (y', Work.Diff.STE.Flat.jetM (V p.1) y') a b) j w p.2

@[simp] lemma xi_apply (V : ℝ → Modl n → Mtrx n) (j : ℕ) (w : Fin j → Fin n) (a b : Fin n)
    (p : ℝ × Modl n) : xi V j w a b p = pdW (fun y' => V p.1 y' a b) j w p.2 := rfl

@[simp] lemma zeta_apply (Φ : Modl n × Work.Diff.STE.Flat.Jet n → Mtrx n)
    (V : ℝ → Modl n → Mtrx n) (j : ℕ) (w : Fin j → Fin n) (a b : Fin n) (p : ℝ × Modl n) :
    zeta Φ V j w a b p = pdW (fun y' => Φ (y', Work.Diff.STE.Flat.jetM (V p.1) y') a b) j w p.2 :=
  rfl

/-- The continuous linear map `v ↦ ∑ c, v c • J c` underlying the derivative of a word
derivative. -/
noncomputable def bLin (J : Fin n → ℂ) : Modl n →L[ℝ] ℂ :=
  ∑ c : Fin n, (ContinuousLinearMap.proj c : Modl n →L[ℝ] ℝ).smulRight (J c)

lemma bLin_apply (J : Fin n → ℂ) (v : Modl n) : bLin J v = ∑ c, v c • J c := by
  simp [bLin, ContinuousLinearMap.sum_apply]

/-- The expansion of a vector in the coordinate frame. -/
lemma sum_single_eq_self_sj (v : Modl n) :
    ∑ c : Fin n, v c • (Pi.single c (1 : ℝ) : Modl n) = v := by
  funext i
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne (Ne.symm hb)]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The derivative of a `ℂ`-valued function on `Modl n` in terms of its values on the coordinate
frame. -/
lemma fderiv_eq_bLin {g : Modl n → ℂ} {y : Modl n} (hg : DifferentiableAt ℝ g y) :
    fderiv ℝ g y = bLin (fun c => fderiv ℝ g y (Pi.single c 1)) := by
  ext v
  have h1 : fderiv ℝ g y v = fderiv ℝ g y (∑ c : Fin n, v c • (Pi.single c (1 : ℝ) : Modl n)) := by
    rw [sum_single_eq_self_sj]
  rw [h1, map_sum, bLin_apply]
  simp

/-- The derivative of a word derivative is the sum of the next word derivatives. -/
lemma fderiv_pdW {f : Modl n → ℂ} {y : Modl n} {j : ℕ} {w : Fin j → Fin n}
    (hd : DifferentiableAt ℝ (pdW f j w) y) :
    fderiv ℝ (pdW f j w) y = bLin (fun c => pdW f (j + 1) (Fin.cons c w) y) := by
  rw [fderiv_eq_bLin hd]
  exact congrArg bLin (funext fun c => (congrFun (pdW_succ_cons f j c w) y).symm)

/-- A word derivative of a smooth function is smooth. -/
lemma contDiffOn_pdW_slice {Ω : Set (Modl n)} (hΩ : IsOpen Ω) {f : Modl n → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (j : ℕ) (w : Fin j → Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (pdW f j w) Ω := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    rw [pdW_succ]
    exact (ih (Fin.tail w)).fderiv_of_isOpen hΩ (by rw [ENat.coe_top_add_one]) |>.clm_apply
      contDiffOn_const

/-! ## Smoothness of the spatial jet of a slice

These are the ingredients which show that the slices of the right hand side `G` are smooth (the
hypothesis `hGs` of `pdW_commute_smooth`). -/

/-- The first coordinate derivative of a smooth matrix valued function is smooth. -/
lemma contDiffOn_pdM_sj {Ω : Set (Modl n)} (hΩ : IsOpen Ω) {u : Modl n → Mtrx n}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) (c : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.Flat.pdM c u) Ω := by
  rw [contDiffOn_pi]
  intro a
  rw [contDiffOn_pi]
  intro b
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Modl n => u y a b) Ω :=
    (contDiffOn_pi.mp ((contDiffOn_pi.mp hu) a)) b
  have h2 : (fun y : Modl n => Work.Diff.STE.Flat.pdM c u y a b) =
      pdW (fun y' => u y' a b) 1 (fun _ => c) := rfl
  rw [h2]
  exact contDiffOn_pdW_slice hΩ h1 1 (fun _ => c)

/-- The second coordinate derivative of a smooth matrix valued function is smooth. -/
lemma contDiffOn_pdM_pdM_sj {Ω : Set (Modl n)} (hΩ : IsOpen Ω) {u : Modl n → Mtrx n}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) (c d : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d u)) Ω := by
  rw [contDiffOn_pi]
  intro a
  rw [contDiffOn_pi]
  intro b
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.Flat.pdM d u) Ω := contDiffOn_pdM_sj hΩ hu d
  have h1' : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Modl n => Work.Diff.STE.Flat.pdM d u y a b) Ω :=
    (contDiffOn_pi.mp ((contDiffOn_pi.mp h1) a)) b
  have h2 : (fun y : Modl n => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d u) y a b) =
      pdW (fun y' => Work.Diff.STE.Flat.pdM d u y' a b) 1 (fun _ => c) := rfl
  rw [h2]
  exact contDiffOn_pdW_slice hΩ h1' 1 (fun _ => c)

/-- The spatial `2`-jet `y ↦ (y, Flat.jetM u y)` of a smooth matrix valued function is smooth. -/
lemma contDiffOn_jetM_sj {Ω : Set (Modl n)} (hΩ : IsOpen Ω) {u : Modl n → Mtrx n}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Modl n => (y, Work.Diff.STE.Flat.jetM u y)) Ω := by
  have hB : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Modl n => fun c => Work.Diff.STE.Flat.pdM c u y) Ω :=
    contDiffOn_pi.mpr fun c => contDiffOn_pdM_sj hΩ hu c
  have hC : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Modl n => fun c d => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d u) y) Ω :=
    contDiffOn_pi.mpr fun c => contDiffOn_pi.mpr fun d => contDiffOn_pdM_pdM_sj hΩ hu c d
  have h : (fun y : Modl n => (y, Work.Diff.STE.Flat.jetM u y)) = fun y : Modl n =>
      (y, (u y, (fun c => Work.Diff.STE.Flat.pdM c u y,
        fun c d => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d u) y))) := rfl
  rw [h]
  exact contDiffOn_id.prodMk (hu.prodMk (hB.prodMk hC))

/-- The slice at time `t` of the right hand side is smooth when `Φ` is smooth. -/
lemma contDiffOn_Gslice_sj {Ω : Set (Modl n)} (hΩ : IsOpen Ω)
    {Φ : Modl n × Work.Diff.STE.Flat.Jet n → Mtrx n} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {u : Modl n → Mtrx n} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => Φ (y, Work.Diff.STE.Flat.jetM u y)) Ω := by
  have h := hΦ.comp_contDiffOn (contDiffOn_jetM_sj hΩ hu)
  simpa [Function.comp_def] using h

theorem contDiffOn_of_solves_jet {n : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n => Φ p))
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {τ : ℝ} (hτ : 0 < τ)
    (V : ℝ → (Fin n → ℝ) → Work.Diff.STE.Flat.MatC n)
    (hslice : ∀ t ∈ Set.Ico (0 : ℝ) τ, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => V t y) Ω)
    (hjet : ∀ (l : List (Fin n)) (a b : Fin n), ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
        Work.Diff.STE.pdList l (fun y => V p.1 y a b) p.2) (Set.Ico (0 : ℝ) τ ×ˢ Ω))
    (heq : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ y ∈ Ω,
        HasDerivWithinAt (fun s : ℝ => V s y) (Φ (y, Work.Diff.STE.Flat.jetM (V t) y))
          (Set.Ico (0 : ℝ) τ) t) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => V p.1 p.2) (Set.Ico (0 : ℝ) τ ×ˢ Ω) := by
  classical
  set S : Set (ℝ × Modl n) := Set.Ico (0 : ℝ) τ ×ˢ Ω with hS
  have hSuniv : UniqueDiffOn ℝ S := (uniqueDiffOn_Ico 0 τ).prod hΩ.uniqueDiffOn
  -- ## the jet chain rule (delegated: `pdW_comp_jet`)
  have hchain : ∀ (j : ℕ) (w : Fin j → Fin n) (a b : Fin n),
      ∃ Ψ : Modl n × (Idx n (j + 2) → ℂ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Ψ ∧
        ∀ (u : Modl n → Mtrx n) (Ω' : Set (Modl n)), IsOpen Ω' → ContDiffOn ℝ (⊤ : ℕ∞) u Ω' →
          ∀ y ∈ Ω',
            pdW (fun y' => Φ (y', Work.Diff.STE.Flat.jetM u y') a b) j w y =
              Ψ (y, compTower u (j + 2) y) := by
    intro j w a b
    exact pdW_comp_jet Φ hΦ j w a b
  -- ## the jet tower of the right hand side is jointly continuous (hypothesis of `pdW_commute`)
  have hG : ∀ m : ℕ, ContinuousOn (fun p : ℝ × Modl n => compTower (Gslice Φ V p.1) m p.2) S := by
    intro m
    rw [continuousOn_pi]
    rintro ⟨⟨a, b⟩, jj, ww⟩
    obtain ⟨Ψ, hΨsm, hΨ⟩ := hchain jj.val ww a b
    have hcont : ContinuousOn (fun p : ℝ × Modl n =>
        Ψ (p.2, compTower (V p.1) (jj.val + 2) p.2)) S :=
      ContinuousOn.comp (hΨsm.continuous.continuousOn (s := Set.univ))
        (continuousOn_snd.prodMk (continuousOn_compTower hjet (jj.val + 2)))
        (fun p _ => trivial)
    refine hcont.congr fun p hp => ?_
    simp only [compTower_apply, Gslice]
    exact hΨ (V p.1) Ω hΩ (hslice p.1 hp.1) p.2 hp.2
  -- ## the invariant: all word derivatives of `V` are `C^m` on the slab
  have step : ∀ m : ℕ,
      (∀ (j : ℕ) (w : Fin j → Fin n) (a b : Fin n), ContDiffOn ℝ m (xi V j w a b) S) →
      (∀ (j : ℕ) (w : Fin j → Fin n) (a b : Fin n), ContDiffOn ℝ (m + 1) (xi V j w a b) S) := by
    intro m ih j w a b
    -- the time-partial derivative is a smooth function of the tower
    have hA : ContDiffOn ℝ m (zeta Φ V j w a b) S := by
      obtain ⟨Ψ, hΨsm, hΨ⟩ := hchain j w a b
      have htower : ContDiffOn ℝ m (fun p : ℝ × Modl n => compTower (V p.1) (j + 2) p.2) S := by
        rw [contDiffOn_pi]
        intro i
        exact ih i.2.1.val i.2.2 i.1.1 i.1.2
      have harg : ContDiffOn ℝ m (fun p : ℝ × Modl n =>
          (p.2, compTower (V p.1) (j + 2) p.2)) S :=
        contDiffOn_snd.prodMk htower
      have hcomp : ContDiffOn ℝ m (fun p : ℝ × Modl n =>
          Ψ (p.2, compTower (V p.1) (j + 2) p.2)) S :=
        ((contDiff_infty.mp hΨsm) m).comp_contDiffOn harg |>.congr fun p _ => rfl
      refine hcomp.congr fun p hp => ?_
      exact hΨ (V p.1) Ω hΩ (hslice p.1 hp.1) p.2 hp.2
    -- the space-partial derivative
    have hB : ContDiffOn ℝ m (fun p : ℝ × Modl n =>
        bLin (fun c => xi V (j + 1) (Fin.cons c w) a b p)) S := by
      have hsum : ContDiffOn ℝ m (fun p : ℝ × Modl n => ∑ c : Fin n,
          (ContinuousLinearMap.proj c : Modl n →L[ℝ] ℝ).smulRight
            (xi V (j + 1) (Fin.cons c w) a b p)) S := by
        refine ContDiffOn.sum fun c _ => ?_
        exact ContDiffOn.smulRight contDiffOn_const (ih (j + 1) (Fin.cons c w) a b)
      refine hsum.congr fun p hp => ?_
      rfl
    -- the time derivative of the word derivative (delegated: `pdW_commute`)
    have hgd : ∀ σ ∈ Set.Ico (0 : ℝ) τ, ∀ y ∈ Ω,
        HasDerivWithinAt (fun σ' => xi V j w a b (σ', y)) (zeta Φ V j w a b (σ, y))
          (Set.Ico (0 : ℝ) τ) σ :=
      fun σ hσ y hy =>
        pdW_commute_smooth hτ hΩ Φ hΦ V hslice
          (fun t ht => contDiffOn_Gslice_sj hΩ hΦ (hslice t ht)) heq hG j w a b σ hσ y hy
    -- the space derivative of the word derivative
    have hgy : ∀ σ ∈ Set.Ico (0 : ℝ) τ, ∀ y ∈ Ω,
        HasFDerivAt (fun y' => xi V j w a b (σ, y'))
          (bLin (fun c => xi V (j + 1) (Fin.cons c w) a b (σ, y))) y := by
      intro σ hσ y hy
      have hsm1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y' => V σ y' a) Ω :=
        (contDiffOn_pi (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (s := Ω) (Φ := fun y' => V σ y')).mp
          (hslice σ hσ) a
      have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun y' => V σ y' a b) Ω :=
        (contDiffOn_pi (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (s := Ω) (Φ := fun y' => V σ y' a)).mp hsm1 b
      have hd : DifferentiableAt ℝ (pdW (fun y' => V σ y' a b) j w) y :=
        ((contDiffOn_pdW_slice hΩ hsm j w).contDiffAt (hΩ.mem_nhds hy)).differentiableAt
          (by simp)
      have hf : fderiv ℝ (pdW (fun y' => V σ y' a b) j w) y =
          bLin (fun c => xi V (j + 1) (Fin.cons c w) a b (σ, y)) := by
        rw [fderiv_pdW hd]
        rfl
      show HasFDerivAt (pdW (fun y' => V σ y' a b) j w) _ y
      rw [← hf]
      exact hd.hasFDerivAt
    exact contDiffOn_succ_of_partial_of_hasFDeriv hSuniv hΩ (ih j w a b) hA hB hgd hgy
  have hM : ∀ m : ℕ, ∀ (j : ℕ) (w : Fin j → Fin n) (a b : Fin n),
      ContDiffOn ℝ m (xi V j w a b) S := by
    intro m
    induction m with
    | zero =>
      intro j w a b
      rw [Nat.cast_zero, contDiffOn_zero]
      exact continuousOn_pdW hjet j w a b
    | succ m ih => exact step m ih
  -- ## conclusion
  have hcomp : ∀ a b : Fin n, ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Modl n => V p.1 p.2 a b) S := by
    intro a b
    rw [contDiffOn_infty]
    intro m
    have h2 : xi V 0 (fun i : Fin 0 => i.elim0) a b = fun p : ℝ × Modl n => V p.1 p.2 a b := by
      funext p
      simp [xi]
    have h := hM m 0 (fun i : Fin 0 => i.elim0) a b
    rwa [h2] at h
  have hfinal : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Modl n => V p.1 p.2) S :=
    (contDiffOn_pi.mpr fun a => contDiffOn_pi.mpr fun b => hcomp a b)
  simpa [hS] using hfinal

end Work.Diff.STE.Lead
