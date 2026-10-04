import Mathlib
import Submission.Work.Diff.STE.Lead.Defs
import Submission.Work.Diff.STE.Lead.CompJetDefs
import Submission.Work.Diff.STE.Lead.CompJet.tower_hasFDerivAt
import Submission.Work.Diff.STE.Lead.CompJet.fderiv_comp_jet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The jet chain rule `pdW_comp_jet`

The target `Work.Diff.STE.Lead.pdW_comp_jet` is the *jet chain rule* used by the bootstrap
`Work.Diff.STE.Lead.contDiffOn_of_solves_jet`: the `j`-th spatial word derivative of
`y ↦ Φ (y, jetM u y)` is a *smooth function of the `(j+2)`-jet tower* of `u` at `y`.

## Proof

The argument is an induction on the length `j` of the word; the content of the induction step is
the chain rule

`∂_c (Ψ ∘ (id, ct_m)) = (D₁Ψ) (∂_c) + (D₂Ψ) (∂_c ct_m)`,

where the derivative of the jet tower map `ct_m` is the *tower scan* `towerScan m`: it shifts the
word of every tower entry by one letter (`Work.Diff.STE.Lead.pdW_hasFDerivAt` for the single word
derivative, `tower_hasFDerivAt` for the whole tower).  Composing that with the derivative of `Ψ`
and evaluating on the `c`-th coordinate direction gives the *jet replacement*

`jetReplace m Ψ c (y, ct_{m+1} y) = (fderiv Ψ (y, ct_m y)) (e_c, ∂_c ct_m)`,

which is again a smooth function of the `(m+1)`-tower (`contDiff_jetReplace`).  This is exactly the
induction step: the `(j+1)`-st word derivative of `Φ (·, jetM u ·)` is the derivative of the
`j`-th one, which the induction hypothesis writes as a smooth function of `ct_{j+2}`, and one
further derivative raises the tower to order `j+3 = (j+1)+2`.

## Vocabulary

`Submission/Work/Diff/STE/Lead/Defs.lean`:
`pdW u j w` is the `j`-th spatial derivative of `u` along the word `w` (first coordinate
outermost): `pdW u (j+1) (Fin.cons c w) = fun y => fderiv ℝ (pdW u j w) y (Pi.single c 1)`, and
`pdW u 0 _ = u`.  `compTower u m y : Idx n m → ℂ` collects the entries of all spatial derivatives
of `u` of order ≤ m, indexed by an entry `(a,b)` of the matrix and a word.

`Submission/Work/Diff/STE/Lead/CompJetDefs.lean`: `towerScan`, `frameLin`, `restrIdx`,
`pdW_hasFDerivAt`, `contDiffOn_pdW`, `jetReplace`.
-/

open scoped ContDiff BigOperators Function Topology
open Set Filter

namespace Work.Diff.STE.Lead

variable {n : ℕ}

/-! ## The base case: reading the `2`-jet off the `2`-tower -/

/-- The empty word, regarded as a word of length `≤ 2`. -/
def wds0 (n : ℕ) : Wds n 2 := ⟨(0 : Fin 3), Fin.elim0⟩

/-- The one letter word `c`, regarded as a word of length `≤ 2`. -/
def wds1 (c : Fin n) : Wds n 2 := ⟨(1 : Fin 3), fun _ : Fin 1 => c⟩

/-- The two letter word `c :: d`, regarded as a word of length `≤ 2`. -/
def wds2 (c d : Fin n) : Wds n 2 := ⟨(2 : Fin 3), Fin.cons c (Fin.cons d Fin.elim0)⟩

/-- Reading the spatial `2`-jet of a matrix valued function off its `2`-tower. -/
noncomputable def jetOf (J : Idx n 2 → ℂ) : Work.Diff.STE.Flat.Jet n :=
  (fun i j => J ((i, j), wds0 n),
   fun c i j => J ((i, j), wds1 c),
   fun c d i j => J ((i, j), wds2 c d))

/-- The `2`-tower of `u` contains the `2`-jet of `u`: this is the definitional unfolding of `pdW`
(and of `pd`/`pdM` in `Submission/Work/Diff/STE/FlatPDE.lean`). -/
lemma jetOf_compTower (u : Modl n → Mtrx n) (y : Modl n) :
    jetOf (compTower u 2 y) = Work.Diff.STE.Flat.jetM u y := rfl

/-- The map `J ↦ jetOf J` is linear (it is a tuple of evaluations). -/
noncomputable def jetOfC : (Idx n 2 → ℂ) →L[ℝ] Work.Diff.STE.Flat.Jet n :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
      ContinuousLinearMap.proj ((i, j), wds0 n))
    (ContinuousLinearMap.prod
      (ContinuousLinearMap.pi fun c => ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
        ContinuousLinearMap.proj ((i, j), wds1 c))
      (ContinuousLinearMap.pi fun c => ContinuousLinearMap.pi fun d => ContinuousLinearMap.pi fun i =>
        ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj ((i, j), wds2 c d)))

/-- The projection onto the `(a,b)`-entry of a matrix. -/
noncomputable def entCLM (a b : Fin n) : Mtrx n →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (φ := fun _ : Fin n => ℂ) b).comp
    (ContinuousLinearMap.proj (φ := fun _ : Fin n => Fin n → ℂ) a)

lemma entCLM_apply (a b : Fin n) (M : Mtrx n) : entCLM a b M = M a b := rfl

/-- The base case of the induction: `Φ (·, jetM u ·) a b` is a smooth function of the `2`-tower
(no differentiability hypothesis on `u` is needed, since `jetOf_compTower` is definitional). -/
lemma contDiff_basePsi (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Mtrx n)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (a b : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Modl n × (Idx n 2 → ℂ) => Φ (p.1, jetOf p.2) a b) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : Modl n × (Idx n 2 → ℂ) => (p.1, jetOf p.2)) :=
    ((ContinuousLinearMap.fst ℝ (Modl n) (Idx n 2 → ℂ)).contDiff).prodMk
      ((jetOfC (n := n)).contDiff.comp
        (ContinuousLinearMap.snd ℝ (Modl n) (Idx n 2 → ℂ)).contDiff)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : Modl n × (Idx n 2 → ℂ) => Φ (p.1, jetOf p.2)) :=
    hΦ.comp h1
  exact (entCLM a b).contDiff.comp h2

/-! ## The value of the jet replacement on a genuine tower -/

/-- The jet replacement evaluated on a genuine jet tower: the restriction `restrIdx` to the lower
order disappears, by `compTower_restrIdx`. -/
lemma jetReplace_compTower (m : ℕ) (Ψ : Modl n × (Idx n m → ℂ) → ℂ) (c : Fin n)
    (u : Modl n → Mtrx n) (y : Modl n) :
    jetReplace m Ψ c (y, compTower u (m + 1) y) =
      fderiv ℝ Ψ (y, compTower u m y)
        (Pi.single c 1, fun i => compTower u (m + 1) y (ishift c i)) := by
  rw [jetReplace_apply]
  have h1 : (y, fun i => compTower u (m + 1) y (restrIdx (Nat.le_succ m) i)) =
      (y, compTower u m y) := by
    refine Prod.ext rfl ?_
    funext i
    exact compTower_restrIdx _ i y
  rw [h1]

/-! ## Smoothness of the jet replacement (auxiliary) -/

private noncomputable def ctjRestrCLM (m : ℕ) : (Idx n (m+1) → ℂ) →L[ℝ] (Idx n m → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (restrIdx (Nat.le_succ m) i)

private noncomputable def ctjShiftCLM (m : ℕ) (c : Fin n) :
    (Idx n (m+1) → ℂ) →L[ℝ] (Idx n m → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ishift c i)

/-- The jet replacement of a smooth `Ψ` is smooth: it is `(y, v) ↦ (fderiv Ψ y) v` composed with
the continuous linear maps `p ↦ (p.1, p.2 ∘ restrIdx)` and `p ↦ (e_c, p.2 ∘ ishift)`. -/
private lemma ctj_contDiff_jetReplace (m : ℕ) (Ψ : Modl n × (Idx n m → ℂ) → ℂ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (c : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (jetReplace m Ψ c) := by
  have hfst : ContDiff ℝ (⊤ : ℕ∞) (fun p : Modl n × (Idx n (m+1) → ℂ) => p.1) :=
    (ContinuousLinearMap.fst ℝ (Modl n) (Idx n (m+1) → ℂ)).contDiff
  have hsnd : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Modl n × (Idx n (m+1) → ℂ) => ctjRestrCLM m p.2) :=
    (ctjRestrCLM (n := n) m).contDiff.comp
      (ContinuousLinearMap.snd ℝ (Modl n) (Idx n (m+1) → ℂ)).contDiff
  have hsh : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Modl n × (Idx n (m+1) → ℂ) => ctjShiftCLM m c p.2) :=
    (ctjShiftCLM (n := n) m c).contDiff.comp
      (ContinuousLinearMap.snd ℝ (Modl n) (Idx n (m+1) → ℂ)).contDiff
  have hcst : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Modl n × (Idx n (m+1) → ℂ) => (Pi.single c 1 : Modl n)) := contDiff_const
  have harg1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Modl n × (Idx n (m+1) → ℂ) => (p.1, ctjRestrCLM m p.2)) := hfst.prodMk hsnd
  have harg2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Modl n × (Idx n (m+1) → ℂ) =>
        ((Pi.single c 1 : Modl n), ctjShiftCLM m c p.2)) := hcst.prodMk hsh
  have hfd : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Modl n × (Idx n (m+1) → ℂ) => fderiv ℝ Ψ (p.1, ctjRestrCLM m p.2)) :=
    (ContDiff.fderiv_right hΨ (by simp)).comp harg1
  exact hfd.clm_apply harg2

/-! ## The induction on the length of the word -/

/-- **The jet chain rule, in the form of the induction.**  For every word `w` of length `k` there
is a smooth `Ψ` with `pdW (Φ ∘ jet) k w = Ψ ∘ (id, compTower · (k+2))`, for every `u` that is
smooth on an open set and every point of that set. -/
theorem pdW_comp_jet_aux {n : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (a b : Fin n) :
    ∀ (k : ℕ) (w : Fin k → Fin n),
      ∃ Ψ : Modl n × (Idx n (k + 2) → ℂ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Ψ ∧
        ∀ (u : Modl n → Mtrx n) (Ω : Set (Modl n)),
          IsOpen Ω → ContDiffOn ℝ (⊤ : ℕ∞) u Ω → ∀ y ∈ Ω,
            pdW (fun y' => Φ (y', Work.Diff.STE.Flat.jetM u y') a b) k w y =
              Ψ (y, compTower u (k + 2) y) := by
  intro k
  induction k with
  | zero =>
    intro w
    exact ⟨fun p => Φ (p.1, jetOf p.2) a b, contDiff_basePsi Φ hΦ a b,
      fun u Ω hΩ hu y hy => rfl⟩
  | succ k ih =>
    intro w
    obtain ⟨Ψ, hΨ, hΨeq⟩ := ih (Fin.tail w)
    refine ⟨jetReplace (k + 2) Ψ (w 0), ctj_contDiff_jetReplace (k + 2) Ψ hΨ (w 0), ?_⟩
    intro u Ω hΩ hu y hy
    -- the `(k+1)`-st derivative of `Φ ∘ jet` is the derivative of the `k`-th one
    have hev : pdW (fun y' => Φ (y', Work.Diff.STE.Flat.jetM u y') a b) k (Fin.tail w)
        =ᶠ[𝓝 y] fun y' => Ψ (y', compTower u (k + 2) y') := by
      filter_upwards [hΩ.mem_nhds hy] with z hz
      exact hΨeq u Ω hΩ hu z hz
    -- the derivative of the jet tower map
    have hT : HasFDerivAt (fun y' => compTower u (k + 2) y')
        (towerScan (k + 2) (compTower u (k + 2 + 1) y)) y :=
      CompJet.tower_hasFDerivAt hΩ hu hy (k + 2)
    -- one step of the chain rule
    have hB := CompJet.fderiv_comp_jet Ψ hΨ hT (v := Pi.single (w 0) 1)
    rw [← Fin.cons_self_tail w, pdW_succ_cons]
    simp only [Fin.cons_zero]
    rw [hev.fderiv_eq, hB,
      towerScan_single (k + 2) (compTower u (k + 2 + 1) y) (w 0),
      ← jetReplace_compTower (k + 2) Ψ (w 0) u y]

/-
GUIDANCE (from the requester).  Vocabulary: `Submission/Work/Diff/STE/Lead/Defs.lean`.
`pdW u j w` is the `j`-th spatial derivative of `u` along the word `w` (first coordinate
outermost): `pdW u (j+1) (Fin.cons c w) = fun y => fderiv ℝ (pdW u j w) y (Pi.single c 1)`, and
`pdW u 0 _ = u`.  `compTower u m y : Idx n m → ℂ` collects the entries of all spatial derivatives
of `u` of order ≤ m, indexed by an entry `(a,b)` of the matrix and a word.

ROUTE (induction on the word length).
(1) Differentiability of the tower map: for `ContDiffOn ℝ ⊤ u Ω` and `y ∈ Ω`,
    `HasFDerivAt (fun y' => compTower u m y')
       (fun v => fun i => ∑ c, v c • compTower u (m+1) y (ishift c i)) y`.
    For one word this follows by induction on `j` from `fderiv ℝ (pdW u j w) y` being the curried
    `(j+1)`-jet (Mathlib: `fderiv_pi`, `iteratedFDeriv`, `ContinuousLinearMap.proj`), together
    with the expansion of the direction in the coordinate basis `v = ∑ c, v c • Pi.single c 1`.
(2) One step of the chain rule: for smooth `Ψ : Modl n × (Idx n m → ℂ) → ℂ`, the function
    `y ↦ Ψ (y, compTower u m y)` has, along the word `c :: w`, the derivative
    `Ψ' (y, compTower u (m+1) y)` for an explicit smooth `Ψ'` (obtained by composing `fderiv Ψ`
    with linear maps).
(3) Assemble the induction on the length of `w`.
-/
theorem pdW_comp_jet {n : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (j : ℕ) (w : Fin j → Fin n) (a b : Fin n) :
    ∃ Ψ : (Fin n → ℝ) × (Work.Diff.STE.Lead.Idx n (j + 2) → ℂ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Ψ ∧
      ∀ (u : (Fin n → ℝ) → Work.Diff.STE.Flat.MatC n) (Ω : Set (Fin n → ℝ)),
        IsOpen Ω → ContDiffOn ℝ (⊤ : ℕ∞) u Ω → ∀ y ∈ Ω,
          Work.Diff.STE.Lead.pdW (fun y' => Φ (y', Work.Diff.STE.Flat.jetM u y') a b) j w y =
            Ψ (y, Work.Diff.STE.Lead.compTower u (j + 2) y) :=
  pdW_comp_jet_aux Φ hΦ a b j w

end Work.Diff.STE.Lead
