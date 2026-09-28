import Mathlib
import Submission.Work.StemsB.collarLambdaPt
import Submission.Work.StemsB.collarClutch

/-!
# `λ_pt ∘ λ_O-pt ≃ id` and `λ_O-pt ∘ λ_pt ≃ id`

The two clutching maps at the shell point,
`collarLambdaPat : F_G = p⁻¹{d_G.1} → F_O = p⁻¹{∞}` and
`collarLambdaOat : F_O → F_G`, are inverse up to homotopy.  Both are restrictions to the fibre
over the shell point of the comparison maps `Φ_O ∘ Ψ_G` and `Φ_G ∘ Ψ_O` of the two fibrewise
trivialisations, so the two fibrewise homotopies `fibTrivH` (of `id` and `Ψ ∘ Φ`) and `fibTrivK`
(of `id` and `Φ ∘ Ψ`) give the claim:

* `k_O`: `id ≃ Φ_O ∘ Ψ_O = λ_pt ∘ λ_O-pt` on the fibre `F_O`, from `fibTrivK` over the outer
  piece;
* `H_G`: `id ≃ Ψ_G ∘ Φ_G = λ_O-pt ∘ λ_pt` on the fibre `F_G`, from `fibTrivH` over the inner
  cube;
* and each of these conjugated by `λ_O-pt` or `λ_pt` respectively, using that the fibrewise
  homotopies preserve the base (hence restrict to the fibre over the shell point).
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-! ## The four maps on the fibre over the shell point -/

/-- The fibre `p ⁻¹'{shell}` over the shell point, included into `p ⁻¹'sphLoopBig b`. -/
def collarInclG (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) :
    C(↥(p ⁻¹' {sphShellPt b}), ↥(p ⁻¹' sphLoopBig b)) :=
  ⟨fun x => ⟨x.1, by
      have hx : p x.1 = sphShellPt b := x.2
      rw [Set.mem_preimage, hx]; exact (sphShellPt_mem_sphLoopCollar b hb).2⟩, by fun_prop⟩

/-- The same for the outer piece. -/
def collarInclO (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) :
    C(↥(p ⁻¹' {sphShellPt b}), ↥(p ⁻¹' sphLoopOuter b)) :=
  ⟨fun x => ⟨x.1, by
      have hx : p x.1 = sphShellPt b := x.2
      rw [Set.mem_preimage, hx]; exact (sphShellPt_mem_sphLoopCollar b hb).1⟩, by fun_prop⟩

/-- `Ψ_O` restricted to the shell point: `F_O = p⁻¹{∞} → p⁻¹{shell}`. -/
def collarSecO (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    C(↥(p ⁻¹' {(dOuter b).1}), ↥(p ⁻¹' {sphShellPt b})) :=
  ⟨fun y => ⟨(fibTrivΨ p (sphLoopOuter b) (dOuter b) hT_O (collarShellPtOuter b hb, y)).1, by
      rw [Set.mem_preimage, Set.mem_singleton_iff, fibTrivΨ_fst]
      rfl⟩, by fun_prop⟩

/-- `(Φ_O)₂` on the fibre over the shell point: `p⁻¹{shell} → F_O`. -/
def collarAlphaO (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    C(↥(p ⁻¹' {sphShellPt b}), ↥(p ⁻¹' {(dOuter b).1})) :=
  (ContinuousMap.snd).comp ((fibTrivΦ p (sphLoopOuter b) (dOuter b) hT_O).comp (collarInclO b hb p))

/-- `Ψ_G` restricted to the shell point: `F_G = p⁻¹{d_G.1} → p⁻¹{shell}`. -/
def collarSecG (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) :
    C(↥(p ⁻¹' {d_G.1}), ↥(p ⁻¹' {sphShellPt b})) :=
  ⟨fun y => ⟨(fibTrivΨ p (sphLoopBig b) d_G hT_G (collarShellPt b hb, y)).1, by
      rw [Set.mem_preimage, Set.mem_singleton_iff, fibTrivΨ_fst]
      rfl⟩, by fun_prop⟩

/-- `(Φ_G)₂` on the fibre over the shell point: `p⁻¹{shell} → F_G`. -/
def collarAlphaG (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) :
    C(↥(p ⁻¹' {sphShellPt b}), ↥(p ⁻¹' {d_G.1})) :=
  (ContinuousMap.snd).comp ((fibTrivΦ p (sphLoopBig b) d_G hT_G).comp (collarInclG b hb p))

/-- `λ_pt` is the composite of the two maps on the shell fibre. -/
theorem collarLambdaPat_eq (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    collarLambdaPat b hb p d_G hT_G hT_O =
      (collarAlphaO b hb p hT_O).comp (collarSecG b hb p d_G hT_G) := rfl

/-- `λ_O-pt` is the composite of the two maps on the shell fibre. -/
theorem collarLambdaOat_eq (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    collarLambdaOat b hb p d_G hT_G hT_O =
      (collarAlphaG b hb p d_G hT_G).comp (collarSecO b hb p hT_O) := rfl

/-! ## The homotopies induced by `fibTrivH` / `fibTrivK` on the shell fibre -/

/-- The `G`-side of `fibTrivH`: `(t, x) ↦ H_G(x, t)`, which stays over the shell point. -/
def collarHshellG (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) :
    C(unitInterval × ↥(p ⁻¹' {sphShellPt b}), ↥(p ⁻¹' {sphShellPt b})) :=
  let w : C(unitInterval × ↥(p ⁻¹' {sphShellPt b}), ↥(p ⁻¹' sphLoopBig b)) :=
    (fibTrivH p (sphLoopBig b) d_G hT_G).comp
      ⟨fun q => (collarInclG b hb p q.2, q.1), by fun_prop⟩
  have h1 : ∀ q, (w q).1 = (fibTrivH p (sphLoopBig b) d_G hT_G (collarInclG b hb p q.2, q.1)).1 :=
    fun q => rfl
  have hmem : ∀ q, (w q).1 ∈ p ⁻¹' {sphShellPt b} := fun q => by
    rw [Set.mem_preimage, Set.mem_singleton_iff, h1 q, fibTrivH_base]
    exact q.2.2
  ⟨fun q => ⟨(w q).1, hmem q⟩, (continuous_subtype_val.comp w.continuous).subtype_mk hmem⟩

/-- The `O`-side of `fibTrivH`: `(t, x) ↦ H_O(x, t)`, which stays over the shell point. -/
def collarHshellO (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    C(unitInterval × ↥(p ⁻¹' {sphShellPt b}), ↥(p ⁻¹' {sphShellPt b})) :=
  let w : C(unitInterval × ↥(p ⁻¹' {sphShellPt b}), ↥(p ⁻¹' sphLoopOuter b)) :=
    (fibTrivH p (sphLoopOuter b) (dOuter b) hT_O).comp
      ⟨fun q => (collarInclO b hb p q.2, q.1), by fun_prop⟩
  have h1 : ∀ q, (w q).1 = (fibTrivH p (sphLoopOuter b) (dOuter b) hT_O (collarInclO b hb p q.2, q.1)).1 :=
    fun q => rfl
  have hmem : ∀ q, (w q).1 ∈ p ⁻¹' {sphShellPt b} := fun q => by
    rw [Set.mem_preimage, Set.mem_singleton_iff, h1 q, fibTrivH_base]
    exact q.2.2
  ⟨fun q => ⟨(w q).1, hmem q⟩, (continuous_subtype_val.comp w.continuous).subtype_mk hmem⟩

theorem collarHshellG_apply (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (q : unitInterval × ↥(p ⁻¹' {sphShellPt b})) :
    (collarHshellG b hb p d_G hT_G q).1
      = (fibTrivH p (sphLoopBig b) d_G hT_G (collarInclG b hb p q.2, q.1)).1 := rfl

theorem collarHshellO_apply (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (q : unitInterval × ↥(p ⁻¹' {sphShellPt b})) :
    (collarHshellO b hb p hT_O q).1
      = (fibTrivH p (sphLoopOuter b) (dOuter b) hT_O (collarInclO b hb p q.2, q.1)).1 := rfl

theorem collarHshellG_zero (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (x : ↥(p ⁻¹' {sphShellPt b})) :
    collarHshellG b hb p d_G hT_G (0, x) = x := by
  apply Subtype.ext
  rw [collarHshellG_apply, fibTrivH_zero]
  rfl

theorem collarHshellG_one (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (x : ↥(p ⁻¹' {sphShellPt b})) :
    collarHshellG b hb p d_G hT_G (1, x)
      = ((collarSecG b hb p d_G hT_G).comp (collarAlphaG b hb p d_G hT_G)) x := by
  apply Subtype.ext
  rw [collarHshellG_apply, fibTrivH_one]
  rw [show (fibTrivΦ p (sphLoopBig b) d_G hT_G (collarInclG b hb p x))
      = (collarShellPt b hb, (fibTrivΦ p (sphLoopBig b) d_G hT_G (collarInclG b hb p x)).2)
      from Prod.ext ?_ rfl]
  · rfl
  · rw [fibTrivΦ_fst]
    exact Subtype.ext x.2

theorem collarHshellO_zero (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (x : ↥(p ⁻¹' {sphShellPt b})) :
    collarHshellO b hb p hT_O (0, x) = x := by
  apply Subtype.ext
  rw [collarHshellO_apply, fibTrivH_zero]
  rfl

theorem collarHshellO_one (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (x : ↥(p ⁻¹' {sphShellPt b})) :
    collarHshellO b hb p hT_O (1, x)
      = ((collarSecO b hb p hT_O).comp (collarAlphaO b hb p hT_O)) x := by
  apply Subtype.ext
  rw [collarHshellO_apply, fibTrivH_one]
  rw [show (fibTrivΦ p (sphLoopOuter b) (dOuter b) hT_O (collarInclO b hb p x))
      = (collarShellPtOuter b hb, (fibTrivΦ p (sphLoopOuter b) (dOuter b) hT_O
          (collarInclO b hb p x)).2)
      from Prod.ext ?_ rfl]
  · rfl
  · rw [fibTrivΦ_fst]
    exact Subtype.ext x.2

/-! ## The `K`-side: `id ≃ Φ ∘ Ψ` on the two fibres -/

theorem collarKfibO_zero (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (y : ↥(p ⁻¹' {(dOuter b).1})) :
    (fibTrivK p (sphLoopOuter b) (dOuter b) hT_O ((collarShellPtOuter b hb, y), 0)).2 = y := by
  simpa using congrArg Prod.snd
    (fibTrivK_zero p (sphLoopOuter b) (dOuter b) hT_O (collarShellPtOuter b hb, y))

theorem collarKfibO_one (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (y : ↥(p ⁻¹' {(dOuter b).1})) :
    (fibTrivK p (sphLoopOuter b) (dOuter b) hT_O ((collarShellPtOuter b hb, y), 1)).2
      = ((collarAlphaO b hb p hT_O).comp (collarSecO b hb p hT_O)) y := by
  rw [fibTrivK_one]
  rfl

theorem collarKfibG_zero (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (y : ↥(p ⁻¹' {d_G.1})) :
    (fibTrivK p (sphLoopBig b) d_G hT_G ((collarShellPt b hb, y), 0)).2 = y := by
  simpa using congrArg Prod.snd
    (fibTrivK_zero p (sphLoopBig b) d_G hT_G (collarShellPt b hb, y))

theorem collarKfibG_one (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (y : ↥(p ⁻¹' {d_G.1})) :
    (fibTrivK p (sphLoopBig b) d_G hT_G ((collarShellPt b hb, y), 1)).2
      = ((collarAlphaG b hb p d_G hT_G).comp (collarSecG b hb p d_G hT_G)) y := by
  rw [fibTrivK_one]
  rfl

/-! ## The four homotopies -/

/-- `H_G`, transported to the shell fibre. -/
def collarHfibG (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(p ⁻¹' {sphShellPt b}))
      ((collarSecG b hb p d_G hT_G).comp (collarAlphaG b hb p d_G hT_G)) where
  toContinuousMap := collarHshellG b hb p d_G hT_G
  map_zero_left := collarHshellG_zero b hb p d_G hT_G
  map_one_left := collarHshellG_one b hb p d_G hT_G

/-- `H_O`, transported to the shell fibre. -/
def collarHfibO (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(p ⁻¹' {sphShellPt b}))
      ((collarSecO b hb p hT_O).comp (collarAlphaO b hb p hT_O)) where
  toContinuousMap := collarHshellO b hb p hT_O
  map_zero_left := collarHshellO_zero b hb p hT_O
  map_one_left := collarHshellO_one b hb p hT_O

/-- `K_O`: `id ≃ Φ_O ∘ Ψ_O = λ_pt ∘ λ_O-pt` on the fibre `F_O`. -/
def collarKfibO (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b))
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(p ⁻¹' {(dOuter b).1}))
      ((collarAlphaO b hb p hT_O).comp (collarSecO b hb p hT_O)) where
  toContinuousMap := (ContinuousMap.snd).comp
    ((fibTrivK p (sphLoopOuter b) (dOuter b) hT_O).comp
      ⟨fun q : unitInterval × ↥(p ⁻¹' {(dOuter b).1}) => ((collarShellPtOuter b hb, q.2), q.1),
        by fun_prop⟩)
  map_zero_left := collarKfibO_zero b hb p hT_O
  map_one_left := collarKfibO_one b hb p hT_O

/-- `K_G`: `id ≃ Φ_G ∘ Ψ_G = λ_O-pt ∘ λ_pt` on the fibre `F_G`. -/
def collarKfibG (b : ℕ) (hb : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(p ⁻¹' {d_G.1}))
      ((collarAlphaG b hb p d_G hT_G).comp (collarSecG b hb p d_G hT_G)) where
  toContinuousMap := (ContinuousMap.snd).comp
    ((fibTrivK p (sphLoopBig b) d_G hT_G).comp
      ⟨fun q : unitInterval × ↥(p ⁻¹' {d_G.1}) => ((collarShellPt b hb, q.2), q.1),
        by fun_prop⟩)
  map_zero_left := collarKfibG_zero b hb p d_G hT_G
  map_one_left := collarKfibG_one b hb p d_G hT_G

/-! ## The theorem -/

theorem collarLambda_homotopy (b : ℕ) (hb : 1 ≤ b) {E : Type} [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    (∃ (H : C(↥(p ⁻¹' {(dOuter b).1}) × unitInterval, ↥(p ⁻¹' {(dOuter b).1}))),
        (∀ y, H (y, 0) = y) ∧
        (∀ y, H (y, 1) = collarLambdaPat b hb p d_G hT_G hT_O
            (collarLambdaOat b hb p d_G hT_G hT_O y))) ∧
    (∃ (K : C(↥(p ⁻¹' {d_G.1}) × unitInterval, ↥(p ⁻¹' {d_G.1}))),
        (∀ y, K (y, 0) = y) ∧
        (∀ y, K (y, 1) = collarLambdaOat b hb p d_G hT_G hT_O
            (collarLambdaPat b hb p d_G hT_G hT_O y))) := by
  constructor
  · -- `F_O`-side: `id ≃ Φ_O Ψ_O ≃ Φ_O (Ψ_G Φ_G) Ψ_O = λ_pt ∘ λ_O-pt`
    let h₁ := collarKfibO b hb p hT_O
    let h₂ : ContinuousMap.Homotopy
        ((collarAlphaO b hb p hT_O).comp (collarSecO b hb p hT_O))
        ((collarAlphaO b hb p hT_O).comp
          (((collarSecG b hb p d_G hT_G).comp (collarAlphaG b hb p d_G hT_G)).comp
            (collarSecO b hb p hT_O))) :=
      (ContinuousMap.Homotopy.refl (collarAlphaO b hb p hT_O)).comp
        ((collarHfibG b hb p d_G hT_G).comp
          (ContinuousMap.Homotopy.refl (collarSecO b hb p hT_O)))
    let h := h₁.trans h₂
    refine ⟨(h.toContinuousMap).comp
        ⟨fun q : ↥(p ⁻¹' {(dOuter b).1}) × unitInterval => (q.2, q.1), by fun_prop⟩, ?_, ?_⟩
    · intro y
      exact h.map_zero_left y
    · intro y
      rw [collarLambdaPat_eq, collarLambdaOat_eq]
      exact h.map_one_left y
  · -- `F_G`-side
    let k₁ := collarKfibG b hb p d_G hT_G
    let k₂ : ContinuousMap.Homotopy
        ((collarAlphaG b hb p d_G hT_G).comp (collarSecG b hb p d_G hT_G))
        ((collarAlphaG b hb p d_G hT_G).comp
          (((collarSecO b hb p hT_O).comp (collarAlphaO b hb p hT_O)).comp
            (collarSecG b hb p d_G hT_G))) :=
      (ContinuousMap.Homotopy.refl (collarAlphaG b hb p d_G hT_G)).comp
        ((collarHfibO b hb p hT_O).comp
          (ContinuousMap.Homotopy.refl (collarSecG b hb p d_G hT_G)))
    let k := k₁.trans k₂
    refine ⟨(k.toContinuousMap).comp
        ⟨fun q : ↥(p ⁻¹' {d_G.1}) × unitInterval => (q.2, q.1), by fun_prop⟩, ?_, ?_⟩
    · intro y
      exact k.map_zero_left y
    · intro y
      rw [collarLambdaPat_eq, collarLambdaOat_eq]
      exact k.map_one_left y

end

end Work.StemsB
