import Mathlib
import Submission.Work.BW.covolume_prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Product form of the pointwise fundamental-domain reduction: for a finite family of full
`ℤ`-lattices `L i ⊆ E`, each equipped with a `ℤ`-basis `b i`, and a point `x : ι → E`, there is
exactly one element `g` of the product lattice `∏ i, L i` such that `g +ᵥ x` lies in the product
of the fundamental domains of the individual bases.  This is the coordinatewise
`existsUnique_vadd_mem_fundamentalDomain_ofZLatticeBasis`, assembled over the index type. -/
theorem pi_existsUnique_vadd_mem_fundamentalDomain {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (L : ι → Submodule ℤ E)
    [∀ i, DiscreteTopology (L i)] [∀ i, IsZLattice ℝ (L i)]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (b : ∀ i, Module.Basis (κ i) ℤ (L i)) (x : ι → E) :
    ∃! g : ↥(Submodule.pi Set.univ L), g +ᵥ x ∈ Set.pi Set.univ
      (fun i => ZSpan.fundamentalDomain ((b i).ofZLatticeBasis ℝ)) := by
  classical
  have h : ∀ i, ∃! v : L i, v +ᵥ x i ∈ ZSpan.fundamentalDomain ((b i).ofZLatticeBasis ℝ) :=
    fun i => existsUnique_vadd_mem_fundamentalDomain_ofZLatticeBasis (b i) (x i)
  let v : ∀ i, L i := fun i => (h i).choose
  have hv : ∀ i, v i +ᵥ x i ∈ ZSpan.fundamentalDomain ((b i).ofZLatticeBasis ℝ) :=
    fun i => (h i).choose_spec.1
  have huniq : ∀ i (y : L i),
      y +ᵥ x i ∈ ZSpan.fundamentalDomain ((b i).ofZLatticeBasis ℝ) → y = v i :=
    fun i => (h i).choose_spec.2
  let g₀ : ↥(Submodule.pi Set.univ L) := ⟨fun i => v i, by
    rw [Submodule.mem_pi]; intro i _; exact (v i).2⟩
  refine ⟨g₀, ?_, ?_⟩
  · show g₀ +ᵥ x ∈ Set.pi Set.univ (fun i => ZSpan.fundamentalDomain ((b i).ofZLatticeBasis ℝ))
    rw [Set.mem_pi]
    intro i _
    exact hv i
  · intro g hg
    apply Subtype.ext
    funext i
    have hgi : (g : ι → E) i ∈ L i := by
      have hgg := g.2
      rw [Submodule.mem_pi] at hgg
      exact hgg i trivial
    have h1 : (g +ᵥ x) i ∈ ZSpan.fundamentalDomain ((b i).ofZLatticeBasis ℝ) := by
      have hg' := hg
      rw [Set.mem_pi] at hg'
      exact hg' i trivial
    have h2 : ((⟨(g : ι → E) i, hgi⟩ : L i)) +ᵥ x i
        ∈ ZSpan.fundamentalDomain ((b i).ofZLatticeBasis ℝ) := by
      rw [Submodule.vadd_def]
      rw [Submodule.vadd_def] at h1
      exact h1
    have := huniq i ⟨(g : ι → E) i, hgi⟩ h2
    exact congrArg (fun w : L i => (w : E)) this

end Work.BW
