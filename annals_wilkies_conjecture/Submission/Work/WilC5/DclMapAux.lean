import Mathlib
import Submission.Work.WilC5.DclMapTools
import Submission.Work.WilC5.realize_iExs_funMapBody_ii
import Submission.Work.WilC5.existsUnique_realize_of_defines

namespace Work.WilC5

open FirstOrder Language

def DefDom {L : FirstOrder.Language} {M : Type} [L.Structure M] {γ : Type} (i : γ → M) : Set M :=
  {s | ∃ φ : L.Formula (γ ⊕ Fin 1), ∀ v : Fin 1 → M, v 0 = s ↔ φ.Realize (Sum.elim i v)}

/-- The set of points definable over a parameter tuple is closed under function symbols, and the
"partial elementary map" sending a parameter to its image extends to this set in a way compatible
with the function symbols. -/
theorem DclMapAux {L : FirstOrder.Language.{0,0}} {M N : Type} [L.Structure M] [L.Structure N]
    {γ : Type} (i : γ → M) (j : γ → N)
    (H : ∀ φ : L.Formula γ, φ.Realize i ↔ φ.Realize j) :
    ∃ (hclosed : ∀ {n : ℕ} (f : L.Functions n) (x : Fin n → M),
        (∀ k, x k ∈ DefDom (L := L) i) → FirstOrder.Language.Structure.funMap f x ∈ DefDom (L := L) i)
      (w : ↥(DefDom (L := L) i) → N),
      Function.Injective w ∧
      (∀ (b : γ) (hb : i b ∈ DefDom (L := L) i), w ⟨i b, hb⟩ = j b) ∧
      (∀ {n : ℕ} (f : L.Functions n) (x : Fin n → M) (hx : ∀ k, x k ∈ DefDom (L := L) i),
        w ⟨FirstOrder.Language.Structure.funMap f x, hclosed f x hx⟩ =
          FirstOrder.Language.Structure.funMap f (fun k => w ⟨x k, hx k⟩)) := by
  classical
  -- The set of definable points is closed under function symbols: given witnesses `φk` for the
  -- arguments, the formula `∃ y, (⋀ φk y_k) ∧ (· = f y)` defines the value of `f`.
  let hclosed : ∀ {n : ℕ} (f : L.Functions n) (x : Fin n → M),
      (∀ k, x k ∈ DefDom (L := L) i) → Structure.funMap f x ∈ DefDom (L := L) i := by
    intro n f x hx
    simp only [DefDom, Set.mem_ofPred_eq] at hx
    choose φk hk using hx
    exact ⟨Formula.iExs (Fin n) (funMapBody f φk),
      fun v => (realize_iExs_funMapBody_ii i f x φk hk v).symm⟩
  -- `Φ x` is a formula defining the singleton `{x}` over the parameters `i`.
  let Φ : ↥(DefDom (L := L) i) → L.Formula (γ ⊕ Fin 1) := fun x => Classical.choose x.2
  have hΦ : ∀ x : ↥(DefDom (L := L) i), ∀ v : Fin 1 → M,
      v 0 = (x : M) ↔ (Φ x).Realize (Sum.elim i v) := fun x => Classical.choose_spec x.2
  -- `W x` is the (unique) point of `N` defined by `Φ x` over the parameters `j`.
  let W : ↥(DefDom (L := L) i) → N := fun x =>
    Classical.choose (ExistsUnique.exists (existsUnique_realize_of_defines i j H (Φ x) x.1 (hΦ x)))
  have hW : ∀ x : ↥(DefDom (L := L) i), (Φ x).Realize (Sum.elim j (fun _ => W x)) := fun x =>
    Classical.choose_spec
      (ExistsUnique.exists (existsUnique_realize_of_defines i j H (Φ x) x.1 (hΦ x)))
  refine ⟨hclosed, W, ?_, ?_, ?_⟩
  · -- injectivity: if `W x = W y`, then `x` and `y` both satisfy `Φ x ∧ Φ y` over `j`, and this
    -- `γ`-formula transfers back to `i`.
    intro x y hxy
    have hηj : (Formula.iExs (Fin 1) (Φ x ⊓ Φ y)).Realize j := by
      rw [Formula.realize_iExs]
      refine ⟨fun _ => W x, ?_⟩
      rw [Formula.realize_inf]
      refine ⟨?_, ?_⟩
      · exact hW x
      · rw [hxy]
        exact hW y
    have hηi : (Formula.iExs (Fin 1) (Φ x ⊓ Φ y)).Realize i := (H _).2 hηj
    rw [Formula.realize_iExs] at hηi
    obtain ⟨q, hq⟩ := hηi
    rw [Formula.realize_inf] at hq
    obtain ⟨hqx, hqy⟩ := hq
    have h1 : q 0 = x.1 := (hΦ x q).2 hqx
    have h2 : q 0 = y.1 := (hΦ y q).2 hqy
    exact Subtype.ext (by rw [← h1, h2])
  · -- the map agrees with `j` on the parameters
    intro b hb
    have hspec : ∀ v : Fin 1 → M, v 0 = i b ↔ (Φ ⟨i b, hb⟩).Realize (Sum.elim i v) :=
      hΦ ⟨i b, hb⟩
    have hr : (Φ ⟨i b, hb⟩).Realize (Sum.elim j (fun _ => j b)) :=
      realize_const_self i j H (Φ ⟨i b, hb⟩) b hspec
    exact ((existsUnique_realize_of_defines i j H (Φ ⟨i b, hb⟩) (i b) hspec).unique hr
      (hW ⟨i b, hb⟩)).symm
  · -- compatibility with the function symbols
    intro n f x hx
    let ψk : Fin n → L.Formula (γ ⊕ Fin 1) := fun k => Φ ⟨x k, hx k⟩
    have hψk : ∀ k, ∀ v : Fin 1 → M, v 0 = x k ↔ (ψk k).Realize (Sum.elim i v) :=
      fun k => hΦ ⟨x k, hx k⟩
    let zs : Fin n → N := fun k => W ⟨x k, hx k⟩
    have hzs : ∀ k, (ψk k).Realize (Sum.elim j (fun _ => zs k)) := fun k => hW ⟨x k, hx k⟩
    -- the explicit existential formula and `Φ (f x)` agree over `i`
    have hspec : ∀ v : Fin 1 → M, v 0 = Structure.funMap f x ↔
        (Φ ⟨Structure.funMap f x, hclosed f x hx⟩).Realize (Sum.elim i v) :=
      hΦ ⟨Structure.funMap f x, hclosed f x hx⟩
    have hagree : ∀ v : Fin 1 → M,
        (Formula.iExs (Fin n) (funMapBody f ψk)).Realize (Sum.elim i v) ↔
          (Φ ⟨Structure.funMap f x, hclosed f x hx⟩).Realize (Sum.elim i v) := by
      intro v
      rw [realize_iExs_funMapBody_ii i f x ψk hψk v]
      exact hspec v
    have hagreej := realize_iff_transfer i j H hagree
    have hexp := realize_iExs_funMapBody_const j f zs ψk hzs
    have hfe : (Φ ⟨Structure.funMap f x, hclosed f x hx⟩).Realize
        (Sum.elim j (fun _ => Structure.funMap f zs)) :=
      (hagreej (fun _ => Structure.funMap f zs)).1 hexp
    exact ((existsUnique_realize_of_defines i j H (Φ ⟨Structure.funMap f x, hclosed f x hx⟩)
      (Structure.funMap f x) hspec).unique hfe
      (hW ⟨Structure.funMap f x, hclosed f x hx⟩)).symm

end Work.WilC5
