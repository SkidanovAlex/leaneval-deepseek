import Mathlib
import Submission.Work.HornFC.nonzero_mem_component
import Submission.Work.HornFC.componentMap_wd

/-!
# `Work.HornB.components_infinite_abstract`

If `g` is continuous on an open set `P ⊆ ℂ`, maps `P` into itself, has infinite fibres over
every nonzero point of `P`, and

* `B i` (`i : Fin q`) are connected components of `P` that are `g`-invariant,
* every point of `P` reaches one of the `B i` under an iterate of `g`,
* there is a connected component `C` of `P` distinct from every `B i`,

then `P` has infinitely many connected components.

The mechanism is the induced self-map `σ` of the (supposedly finite) set `Ω` of components:
`σ D` is the component containing `g '' D`, well defined because `g '' D` is preconnected.  The
infinite-fibre hypothesis forces `σ` to be *surjective* (a nonzero point `v` of `D` has a preimage
`ζ ∈ P`, and the component of `ζ` is mapped by `σ` onto the component of `v`, i.e. onto `D`).  A
surjective self-map of a finite set is injective.  But `hreach` says `σ^[n] C = B i` for some `n`,
`i`, while `σ (B i) = B i` (invariance) gives `σ^[n] (B i) = B i`; injectivity of `σ^[n]` then
yields `C = B i`, contradicting `hnotall`.
-/

namespace Work.HornB

open Set

noncomputable section

/-- A choice of point of a nonempty subset of `ℂ` (`0` for the empty set).  Its advantage over
`Exists.choose` is that the term `pick C` does not depend on a *proof* that `C` is nonempty, so it
can be rewritten without dependency problems. -/
def pick (C : Set ℂ) : ℂ := by
  classical
  exact if h : C.Nonempty then h.choose else 0

theorem pick_mem {C : Set ℂ} (hC : C.Nonempty) : pick C ∈ C := by
  rw [pick, dite_eq_left hC]
  exact hC.choose_spec

theorem components_infinite_abstract {P : Set ℂ} {g : ℂ → ℂ} {q : ℕ}
    (hPopen : IsOpen P) (hcont : ContinuousOn g P) (hmap : Set.MapsTo g P P)
    (hfiber : ∀ w ∈ P, w ≠ 0 → (g ⁻¹' {w} ∩ P).Infinite)
    (B : Fin q → Set ℂ)
    (hBcomp : ∀ i, ∃ z ∈ P, B i = connectedComponentIn P z)
    (hBinv : ∀ i, Set.MapsTo g (B i) (B i))
    (hreach : ∀ z ∈ P, ∃ n : ℕ, ∃ i : Fin q, g^[n] z ∈ B i)
    (hnotall : ∃ C : Set ℂ, (∃ z ∈ P, C = connectedComponentIn P z) ∧ ∀ i, C ≠ B i) :
    ¬ ∃ s : Finset (Set ℂ), ∀ z ∈ P, connectedComponentIn P z ∈ s := by
  rintro ⟨s, hs⟩
  classical
  -- the (supposedly finite) set of connected components of `P`
  set Ω : Set (Set ℂ) := {C | ∃ z ∈ P, C = connectedComponentIn P z} with hΩdef
  have hΩfin : Ω.Finite := (s.finite_toSet).subset (fun C hC => by
    obtain ⟨z, hz, rfl⟩ := hC
    exact hs z hz)
  haveI : Fintype Ω := hΩfin.fintype
  have hpoint : ∀ (C : Set ℂ), C ∈ Ω → pick C ∈ C := fun C hC => by
    obtain ⟨z, hzP, hCeq⟩ := hC
    have hne : C.Nonempty := ⟨z, by rw [hCeq]; exact mem_connectedComponentIn hzP⟩
    exact pick_mem hne
  have hnonzero : ∀ C ∈ Ω, ∃ w ∈ C, w ≠ 0 := fun C hC => by
    obtain ⟨z, hz, rfl⟩ := hC
    exact Work.HornFC.nonzero_mem_component hPopen hz
  -- `g` sends each component of `P` into a single component of `P`
  have hCmap : ∀ C ∈ Ω, ∀ z ∈ C, ∀ z' ∈ C,
      connectedComponentIn P (g z) = connectedComponentIn P (g z') :=
    fun C hC z hz z' hz' => Work.HornFC.componentMap_wd hPopen hcont hmap hC hz hz'
  have hCmem : ∀ C ∈ Ω, ∀ z ∈ C, connectedComponentIn P (g z) ∈ Ω := fun C hC z hz => by
    obtain ⟨z₀, hz₀, hCeq⟩ := hC
    have hz' : z ∈ connectedComponentIn P z₀ := hCeq ▸ hz
    exact ⟨g z, hmap (connectedComponentIn_subset P z₀ hz'), rfl⟩
  -- the induced map on components of `P`
  let σ : Ω → Ω := fun C => ⟨connectedComponentIn P (g (pick C.1)),
    hCmem C.1 C.2 (pick C.1) (hpoint C.1 C.2)⟩
  have hσ_val : ∀ (C : Ω) {z : ℂ} (hz : z ∈ C.1),
      (σ C).1 = connectedComponentIn P (g z) :=
    fun C z hz => hCmap C.1 C.2 (pick C.1) (hpoint C.1 C.2) z hz
  -- `σ` is surjective: the component of a preimage of a point of `D` maps to `D`
  have hσsurj : Function.Surjective σ := by
    rintro ⟨C', hC'Ω⟩
    obtain ⟨z, hzP, rfl⟩ := hC'Ω
    obtain ⟨v, hvC', hv0⟩ := hnonzero (connectedComponentIn P z) ⟨z, hzP, rfl⟩
    have hvP : v ∈ P := connectedComponentIn_subset P z hvC'
    obtain ⟨ζ, hζg, hζP⟩ := (hfiber v hvP hv0).nonempty
    have hζg' : g ζ = v := Set.mem_singleton_iff.mp hζg
    refine ⟨⟨connectedComponentIn P ζ, ⟨ζ, hζP, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    rw [hσ_val ⟨connectedComponentIn P ζ, ⟨ζ, hζP, rfl⟩⟩ (mem_connectedComponentIn hζP),
      hζg']
    exact (connectedComponentIn_eq hvC').symm
  have hσinj : Function.Injective σ := Finite.injective_iff_surjective.mpr hσsurj
  -- `σ^[n]` acts on the representative point by `g^[n]`
  have hσpow : ∀ (C' : Ω) (n : ℕ),
      (σ^[n] C').1 = connectedComponentIn P (g^[n] (pick C'.1)) := by
    intro C' n
    induction n with
    | zero =>
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
      obtain ⟨z, hzP, hCeq⟩ := C'.2
      have hmem : pick C'.1 ∈ C'.1 := hpoint C'.1 C'.2
      have hmem' : pick C'.1 ∈ connectedComponentIn P z := by
        rw [← hCeq]; exact hmem
      exact hCeq.trans (connectedComponentIn_eq hmem')
    | succ n ih =>
      rw [Function.iterate_succ_apply' σ n C', Function.iterate_succ_apply' g n (pick C'.1),
        hσ_val (σ^[n] C') (hpoint (σ^[n] C').1 (σ^[n] C').2)]
      have hpickP : pick C'.1 ∈ P := by
        obtain ⟨z, hzP, hCeq⟩ := C'.2
        have hmem : pick C'.1 ∈ connectedComponentIn P z := by
          rw [← hCeq]; exact hpoint C'.1 C'.2
        exact connectedComponentIn_subset P z hmem
      have hgnmem : g^[n] (pick C'.1) ∈ (σ^[n] C').1 := by
        rw [ih]
        exact mem_connectedComponentIn (hmap.iterate n hpickP)
      rw [hCmap (σ^[n] C').1 (σ^[n] C').2
        (pick (σ^[n] C').1) (hpoint (σ^[n] C').1 (σ^[n] C').2)
        (g^[n] (pick C'.1)) hgnmem]
  -- the privileged components `B i` as elements of `Ω`
  let Bi : Fin q → Ω := fun i => ⟨B i, hBcomp i⟩
  -- `σ` fixes each `B i` (invariance)
  have hσBi : ∀ i : Fin q, σ (Bi i) = Bi i := by
    intro i
    apply Subtype.ext
    rw [hσ_val (Bi i) (hpoint (B i) (Bi i).2)]
    obtain ⟨z, hzP, hzB⟩ := hBcomp i
    have hmem : g (pick (B i)) ∈ connectedComponentIn P z := by
      rw [← hzB]
      exact hBinv i (hpoint (B i) (Bi i).2)
    exact (connectedComponentIn_eq hmem).symm.trans hzB.symm
  -- iterates of `σ` fix each `B i`
  have hσnBi_fix : ∀ (i : Fin q) (n : ℕ), σ^[n] (Bi i) = Bi i := by
    intro i n
    induction n with
    | zero => rw [Function.iterate_zero_apply]
    | succ n ih => rw [Function.iterate_succ_apply', ih, hσBi i]
  -- the component `C` outside the `B i`, which nonetheless reaches a `B i`
  obtain ⟨C, hCΩ, hCne⟩ := hnotall
  have hpickC : pick C ∈ P := by
    have hpmem : pick C ∈ C := hpoint C hCΩ
    obtain ⟨z, hzP, hCeq⟩ := hCΩ
    have hmem : pick C ∈ connectedComponentIn P z := by
      rw [← hCeq]; exact hpmem
    exact connectedComponentIn_subset P z hmem
  obtain ⟨n, i, hn⟩ := hreach (pick C) hpickC
  have hσnC : σ^[n] (⟨C, hCΩ⟩ : Ω) = Bi i := by
    apply Subtype.ext
    rw [hσpow ⟨C, hCΩ⟩ n]
    obtain ⟨z, hzP, hzB⟩ := hBcomp i
    have hmem : g^[n] (pick C) ∈ connectedComponentIn P z := by
      rw [← hzB]
      exact hn
    exact (connectedComponentIn_eq hmem).symm.trans hzB.symm
  -- injectivity of `σ^[n]` gives `C = B i`, contradicting `hnotall`
  have heq : (⟨C, hCΩ⟩ : Ω) = Bi i :=
    (hσinj.iterate n) (hσnC.trans (hσnBi_fix i n).symm)
  exact hCne i (congrArg Subtype.val heq)

end

end Work.HornB
