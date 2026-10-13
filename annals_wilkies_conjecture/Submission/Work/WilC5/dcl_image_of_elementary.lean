import Mathlib
import Submission.Work.WilC2.Dcl

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC5

open WilkiesDesign.CG

/-- **Elementary embeddings preserve closedness under definable closure.**

If `A ⊆ K` is closed under definable closure (`Dcl A ⊆ A`), then so is its image `f '' A` under an
`LRc`-elementary embedding `f : K ↪ₑ N`.

The proof picks, for each parameter `p ∈ f '' A`, a preimage `τ p ∈ A`, `f (τ p) = p`.  If
`φ : LRc.Formula ((f '' A) ⊕ Fin 1)` defines the singleton `{y}` over `f '' A`, then
`f.map_formula` shows that `φ (τ, u) ↔ f (u 0) = y` for every `u : Fin 1 → K`, and the
existential-uniqueness formula `φ.iExsUnique (Fin 1)` holds in `N` at the parameters `f '' A`, hence
— again by elementarity — in `K` at the parameters `τ`.  So some `u 0 ∈ K` satisfies `φ (τ, u 0)`,
hence `f (u 0) = y`; and since `φ (τ, ·)` defines a singleton over the parameters `τ` in `A`,
`u 0 ∈ Dcl A ⊆ A`.  Thus `y ∈ f '' A`. -/
theorem dcl_image_of_elementary {K N : Type}
    [FirstOrder.Language.Structure WilkiesDesign.CG.LRc K]
    [FirstOrder.Language.Structure WilkiesDesign.CG.LRc N]
    (f : @FirstOrder.Language.ElementaryEmbedding WilkiesDesign.CG.LRc K N _ _) {A : Set K}
    (hA : Work.WilC2.Dcl A ⊆ A) :
    @Work.WilC2.Dcl N _ ((⇑f) '' A) ⊆ (⇑f) '' A := by
  intro y hy
  rw [Work.WilC2.mem_dcl] at hy
  unfold Set.Definable₁ at hy
  rw [Set.definable_iff_exists_formula_sum] at hy
  obtain ⟨φ, hφ⟩ := hy
  -- `φ` defines the singleton `{y}` over the parameters `f '' A`
  have hφ' : ∀ v : Fin 1 → N,
      (v 0 = y) ↔ φ.Realize (Sum.elim ((↑) : ((⇑f) '' A) → N) v) := by
    intro v
    have h := (Set.ext_iff.mp hφ) v
    simpa using h
  -- choose preimages in `A`
  have hchoice : ∀ p : ((⇑f) '' A), ∃ a : K, a ∈ A ∧ f a = (p : N) := by
    rintro ⟨p, a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  let τA : ((⇑f) '' A) → A :=
    fun p => ⟨Classical.choose (hchoice p), (Classical.choose_spec (hchoice p)).1⟩
  let τ : ((⇑f) '' A) → K := fun p => (τA p : K)
  have hτf : ∀ p : ((⇑f) '' A), f (τ p) = (p : N) :=
    fun p => (Classical.choose_spec (hchoice p)).2
  -- elementarity turns `φ` at the parameters `τ` into `φ` at the parameters `f '' A`
  have htrans : ∀ u : Fin 1 → K, φ.Realize (Sum.elim τ u) ↔ f (u 0) = y := by
    intro u
    have h1 := f.map_formula φ (Sum.elim τ u)
    rw [show f ∘ (Sum.elim τ u) = Sum.elim ((↑) : ((⇑f) '' A) → N) (f ∘ u) from by
      funext a; cases a with
      | inl p => exact hτf p
      | inr i => rfl] at h1
    exact h1.symm.trans ((hφ' (f ∘ u)).symm)
  -- `∃! v, φ (·, v)` holds in `N` at the parameters `f '' A`
  have hχN : (φ.iExsUnique (Fin 1)).Realize ((↑) : ((⇑f) '' A) → N) := by
    rw [Formula.realize_iExsUnique]
    refine ⟨fun _ : Fin 1 => y, ?_, ?_⟩
    · exact (hφ' (fun _ : Fin 1 => y)).mp rfl
    · intro j hj
      funext k
      have hk : j 0 = y := (hφ' j).mpr hj
      have hk0 : k = 0 := Subsingleton.elim k 0
      rw [hk0]
      exact hk
  -- hence it holds in `K` at the parameters `τ`
  have hχK : (φ.iExsUnique (Fin 1)).Realize τ := by
    have h := f.map_formula (φ.iExsUnique (Fin 1)) τ
    rw [show f ∘ τ = ((↑) : ((⇑f) '' A) → N) from funext (fun p => hτf p)] at h
    exact h.mp hχN
  obtain ⟨u, hu, huniq⟩ := Formula.realize_iExsUnique.mp hχK
  -- `φ (τ, ·)` defines the singleton `{u 0}` over the parameters `τ ⊆ A`
  have hsing : ∀ w : Fin 1 → K, (w 0 = u 0) ↔ φ.Realize (Sum.elim τ w) := by
    intro w
    constructor
    · intro hw
      have hwu : w = u := by
        funext k
        have hk : k = 0 := Subsingleton.elim k 0
        rw [hk, hw]
      rw [hwu]
      exact hu
    · intro hw
      rw [huniq w hw]
  have hDcl : u 0 ∈ Work.WilC2.Dcl A := by
    rw [Work.WilC2.mem_dcl, Set.Definable₁, Set.definable_iff_exists_formula_sum]
    refine ⟨φ.relabel (Sum.map τA id), ?_⟩
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    rw [Formula.realize_relabel]
    rw [show (((Sum.elim ((↑) : A → K)) w) ∘ Sum.map τA id) = Sum.elim τ w from by
      funext a; cases a with
      | inl p => rfl
      | inr i => rfl]
    exact hsing w
  exact ⟨u 0, hA hDcl, (htrans u).mp hu⟩

end Work.WilC5
