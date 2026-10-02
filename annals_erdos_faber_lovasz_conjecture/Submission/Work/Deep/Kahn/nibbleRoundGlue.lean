import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.NibbleRoundDefs

/-!
# Glue: the regularised one-round step and the embedding give the general one-round step

`Work.Deep.Kahn.nibbleRoundGlue` derives `RoundStepStatement` (the one-round nibble step for an
arbitrary linear hypergraph with edges of size at most `C`, lists of common size `Λ` and colour
degrees at most `D`) from the two inputs of `Work.Deep.Kahn.NibbleRoundDefs`:

* `EmbeddingStatement` (`prop:embedding`): the instance is embedded into a *regularised* instance,
* `RegularisedNibbleStatement`: the one-round analysis in the regularised instance.

The proof is a transport along the embedding `(ι, ρ)`: the kept subhypergraph of the embedded
instance is pulled back along `ι`, the colour of a pulled back kept edge is the `ρ`-preimage of
the colour of its image (`ρ` is injective and the lists are `ρ`-images of the original lists),
and the new lists are the traces of the embedded new lists on `range ρ`.  The numerical
estimates (`newLambda`, `newDeg`) transfer verbatim because the embedding is applied with the
*same* parameters `C, D, Λ, K`; the colour-degree estimate is transferred along the injection
`e ↦ ι e` between the uncoloured edges.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

theorem nibbleRoundGlue (hA : Work.Deep.Kahn.RegularisedNibbleStatement) (hB : Work.Deep.Kahn.EmbeddingStatement) : Work.Deep.Kahn.RoundStepStatement := by
  intro C hC ε η hε hη
  obtain ⟨Dmin, hDminpos, hDminbd, hDmin⟩ := hA C hC ε η hε hη
  refine ⟨Dmin, hDminpos, hDminbd, ?_⟩
  intro n c 𝓗 L D Λ K hD1 hΛ1 hK2 hηK h16 hlin hsze hLcard hCdeg hεD hΛ10 hDminD hlogK hKlog2 hCKη
  -- the embedding of the instance into a regularised one
  obtain ⟨n', c', 𝓗', L₁, emb, ι, ρ, _hinjEmb, hinjι, hinjρ, hlin', hsze', hLcard', hLimg,
    hinc, hint, hdegex, _hdegmono⟩ := hB n c 𝓗 L C D Λ hC hD1 hΛ1 hlin hsze hLcard hCdeg
  -- the one-round step in the regularised instance
  obtain ⟨𝓗'₀, hsub', φ', L₂, cond1, cond2, cond3, cond4, cond5⟩ :=
    hDmin n' c' 𝓗' L₁ D Λ K hD1 hΛ1 hK2 hηK h16 hlin' hsze' hLcard' hdegex hεD hΛ10 hDminD
      hlogK hKlog2 hCKη
  classical
  -- the kept subhypergraph of `𝓗`, pulled back along `ι`
  let 𝒢₀ : ErdosFaberLovaszConjecture.Hypergraph (Fin n) :=
    {e | e ∈ 𝓗 ∧ ∀ he : e ∈ 𝓗, (ι ⟨e, he⟩ : Set (Fin n')) ∈ 𝓗'₀}
  have hsub : 𝒢₀ ⊆ 𝓗 := fun e he => he.1
  -- the two lifts of the embedding to the subtypes of kept resp. uncoloured edges
  let κ : ↥𝒢₀ → ↥𝓗'₀ := fun f =>
    ⟨(ι ⟨(f : Set (Fin n)), f.2.1⟩ : Set (Fin n')), f.2.2 f.2.1⟩
  have hκval : ∀ f : ↥𝒢₀,
      (κ f : Set (Fin n')) = (ι ⟨(f : Set (Fin n)), f.2.1⟩ : Set (Fin n')) := fun _ => rfl
  let κ' : ↥(𝓗 \ 𝒢₀) → ↥(𝓗' \ 𝓗'₀) := fun E =>
    ⟨(ι ⟨(E : Set (Fin n)), E.2.1⟩ : Set (Fin n')),
      ⟨(ι ⟨(E : Set (Fin n)), E.2.1⟩).2, by
        intro hcon
        exact E.2.2 ⟨E.2.1, fun _ => hcon⟩⟩⟩
  have hκ'val : ∀ E : ↥(𝓗 \ 𝒢₀),
      (κ' E : Set (Fin n')) = (ι ⟨(E : Set (Fin n)), E.2.1⟩ : Set (Fin n')) := fun _ => rfl
  have hκ'inj : Function.Injective κ' := by
    intro E₁ E₂ h1
    apply Subtype.ext
    have h1v : (κ' E₁ : Set (Fin n')) = (κ' E₂ : Set (Fin n')) :=
      congrArg (fun z : ↥(𝓗' \ 𝓗'₀) => (z : Set (Fin n'))) h1
    rw [hκ'val E₁, hκ'val E₂] at h1v
    have h2 : ι ⟨(E₁ : Set (Fin n)), E₁.2.1⟩ = ι ⟨(E₂ : Set (Fin n)), E₂.2.1⟩ :=
      Subtype.ext h1v
    exact congrArg (fun z : ↥𝓗 => (z : Set (Fin n))) (hinjι h2)
  -- the colour of a pulled back kept edge, as the `ρ`-preimage of the colour of its image
  have hex : ∀ f : ↥𝒢₀,
      ∃ γ : Fin c, γ ∈ L ⟨(f : Set (Fin n)), hsub f.2⟩ ∧ ρ γ = φ'.labels (κ f) := by
    intro f
    have h1 : φ'.labels (κ f) ∈ (L ⟨(f : Set (Fin n)), hsub f.2⟩).image ρ := by
      have h2 : φ'.labels (κ f) ∈ L₁ (ι ⟨(f : Set (Fin n)), f.2.1⟩) := cond1 (κ f)
      rw [hLimg ⟨(f : Set (Fin n)), f.2.1⟩] at h2
      exact h2
    obtain ⟨γ, hγ, hργ⟩ := Finset.mem_image.mp h1
    exact ⟨γ, hγ, hργ⟩
  let ψ : ↥𝒢₀ → Fin c := fun f => Classical.choose (hex f)
  have hψmem : ∀ f : ↥𝒢₀, ψ f ∈ L ⟨(f : Set (Fin n)), hsub f.2⟩ :=
    fun f => (Classical.choose_spec (hex f)).1
  have hψρ : ∀ f : ↥𝒢₀, ρ (ψ f) = φ'.labels (κ f) :=
    fun f => (Classical.choose_spec (hex f)).2
  -- the pulled back colouring
  let φ : 𝒢₀.Coloring (Fin c) :=
    { labels := ψ
      isColoring := by
        intro f₁ f₂ hne hnon heq
        have hρeq : φ'.labels (κ f₁) = φ'.labels (κ f₂) := by
          rw [← hψρ f₁, ← hψρ f₂, heq]
        have hne' : κ f₁ ≠ κ f₂ := by
          intro hEq
          apply hne
          have hv : (κ f₁ : Set (Fin n')) = (κ f₂ : Set (Fin n')) :=
            congrArg (fun x : ↥𝓗'₀ => (x : Set (Fin n'))) hEq
          rw [hκval f₁, hκval f₂] at hv
          have h2 : ι ⟨(f₁ : Set (Fin n)), f₁.2.1⟩ = ι ⟨(f₂ : Set (Fin n)), f₂.2.1⟩ :=
            Subtype.ext hv
          have hval : (f₁ : Set (Fin n)) = (f₂ : Set (Fin n)) :=
            congrArg (fun x : ↥𝓗 => (x : Set (Fin n))) (hinjι h2)
          exact Subtype.ext hval
        have hne2 : (⟨(f₁ : Set (Fin n)), f₁.2.1⟩ : ↥𝓗) ≠ ⟨(f₂ : Set (Fin n)), f₂.2.1⟩ := by
          intro h
          apply hne
          exact Subtype.ext (congrArg (fun x : ↥𝓗 => (x : Set (Fin n))) h)
        have hnon' : ((κ f₁ : Set (Fin n')) ∩ (κ f₂ : Set (Fin n'))).Nonempty :=
          hint _ _ hne2 hnon
        exact φ'.isColoring (κ f₁) (κ f₂) hne' hnon' hρeq }
  -- the pulled back lists: the trace of the embedded new lists on `range ρ`
  let Lnew : ↥(𝓗 \ 𝒢₀) → Finset (Fin c) := fun E =>
    Finset.univ.filter (fun γ => ρ γ ∈ L₂ (κ' E))
  have hLnewmem : ∀ (E : ↥(𝓗 \ 𝒢₀)) (γ : Fin c), γ ∈ Lnew E ↔ ρ γ ∈ L₂ (κ' E) := by
    intro E γ
    show γ ∈ Finset.univ.filter (fun γ : Fin c => ρ γ ∈ L₂ (κ' E)) ↔ ρ γ ∈ L₂ (κ' E)
    simp
  have hsubL : ∀ E : ↥(𝓗 \ 𝒢₀), Lnew E ⊆ L ⟨(E : Set (Fin n)), E.2.1⟩ := by
    intro E γ hγ
    have h1 : ρ γ ∈ L₁ (ι ⟨(E : Set (Fin n)), E.2.1⟩) :=
      (cond2 (κ' E)) ((hLnewmem E γ).mp hγ)
    rw [hLimg ⟨(E : Set (Fin n)), E.2.1⟩] at h1
    obtain ⟨γ₀, hγ₀, hρ⟩ := Finset.mem_image.mp h1
    rwa [hinjρ hρ] at hγ₀
  have hcard : ∀ E : ↥(𝓗 \ 𝒢₀), (Lnew E).card = (L₂ (κ' E)).card := by
    intro E
    have himg : (Lnew E).image ρ = L₂ (κ' E) := by
      apply Finset.Subset.antisymm
      · intro y hy
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hy
        exact (hLnewmem E γ).mp hγ
      · intro y hy
        have h1 : y ∈ L₁ (ι ⟨(E : Set (Fin n)), E.2.1⟩) := (cond2 (κ' E)) hy
        rw [hLimg ⟨(E : Set (Fin n)), E.2.1⟩] at h1
        obtain ⟨γ₀, hγ₀, hρ⟩ := Finset.mem_image.mp h1
        exact Finset.mem_image.mpr ⟨γ₀, (hLnewmem E γ₀).mpr (by rw [hρ]; exact hy), hρ⟩
    rw [← himg, Finset.card_image_of_injOn (Set.injOn_of_injective hinjρ)]
  have hsize : ∀ E : ↥(𝓗 \ 𝒢₀),
      newLambda Λ C D K - η * (Λ : ℝ) ≤ ((Lnew E).card : ℝ) := by
    intro E
    rw [hcard E]
    exact cond3 (κ' E)
  have havoid : ∀ E : ↥(𝓗 \ 𝒢₀), ∀ f : ↥𝒢₀,
      (((f : Set (Fin n)) ∩ (E : Set (Fin n))).Nonempty → ψ f ∉ Lnew E) := by
    intro E f hnon hmem
    have h1 : φ'.labels (κ f) ∈ L₂ (κ' E) := by
      rw [← hψρ f]
      exact (hLnewmem E (ψ f)).mp hmem
    have hne : (⟨(f : Set (Fin n)), f.2.1⟩ : ↥𝓗) ≠ ⟨(E : Set (Fin n)), E.2.1⟩ := by
      intro h
      have hval : (f : Set (Fin n)) = (E : Set (Fin n)) :=
        congrArg (fun x : ↥𝓗 => (x : Set (Fin n))) h
      exact E.2.2 (hval ▸ f.2)
    have hnon' : ((κ f : Set (Fin n')) ∩ (κ' E : Set (Fin n'))).Nonempty := hint _ _ hne hnon
    exact cond4 (κ' E) (κ f) hnon' h1
  -- the colour-degree estimate, transferred along `e ↦ ι e`
  have hdeg : ∀ x : Fin n, ∀ γ : Fin c,
      ((Nat.card {E : ↥(𝓗 \ 𝒢₀) // x ∈ (E : Set (Fin n)) ∧ γ ∈ Lnew E} : ℕ) : ℝ) ≤
        newDeg Λ C D K + η * (D : ℝ) := by
    intro x γ
    have hle : Nat.card {E : ↥(𝓗 \ 𝒢₀) // x ∈ (E : Set (Fin n)) ∧ γ ∈ Lnew E} ≤
        Nat.card {E' : ↥(𝓗' \ 𝓗'₀) //
          emb x ∈ (E' : Set (Fin n')) ∧ ρ γ ∈ L₂ E'} := by
      have key : ∀ E : {E : ↥(𝓗 \ 𝒢₀) // x ∈ (E : Set (Fin n)) ∧ γ ∈ Lnew E},
          (emb x ∈ (κ' E.1 : Set (Fin n'))) ∧ (ρ γ ∈ L₂ (κ' E.1)) := by
        intro E
        constructor
        · exact hinc x ⟨(E.1 : Set (Fin n)), E.1.2.1⟩ E.2.1
        · exact (hLnewmem E.1 γ).mp E.2.2
      refine Nat.card_le_card_of_injective
        (fun E => ⟨κ' E.1, (key E).1, (key E).2⟩) ?_
      intro E₁ E₂ hEq
      have hκeq : κ' E₁.1 = κ' E₂.1 := by
        have h := congrArg (fun z : {E' : ↥(𝓗' \ 𝓗'₀) //
            emb x ∈ (E' : Set (Fin n')) ∧ ρ γ ∈ L₂ E'} => (z : ↥(𝓗' \ 𝓗'₀))) hEq
        exact h
      exact Subtype.ext (hκ'inj hκeq)
    calc ((Nat.card {E : ↥(𝓗 \ 𝒢₀) // x ∈ (E : Set (Fin n)) ∧ γ ∈ Lnew E} : ℕ) : ℝ)
        ≤ ((Nat.card {E' : ↥(𝓗' \ 𝓗'₀) //
            emb x ∈ (E' : Set (Fin n')) ∧ ρ γ ∈ L₂ E'} : ℕ) : ℝ) := by
          exact_mod_cast hle
      _ ≤ newDeg Λ C D K + η * (D : ℝ) := cond5 (emb x) (ρ γ)
  exact ⟨𝒢₀, hsub, φ, Lnew, hψmem, hsubL, hsize, havoid, hdeg⟩

end Work.Deep.Kahn
