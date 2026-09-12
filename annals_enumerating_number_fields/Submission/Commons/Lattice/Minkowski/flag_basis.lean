import Mathlib.Algebra.Module.ZLattice.Basic
import Submission.Commons.Lattice.Module.basis_extension_pure_rank

open Module Submodule
open scoped BigOperators
set_option autoImplicit false

noncomputable section

namespace Commons.Lattice.Minkowski

namespace flagBasis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A submodule of a discrete submodule is discrete (general ambient space version). -/
lemma discreteTopology_of_le_general {L L' : Submodule ℤ E} (hle : L' ≤ L)
    [DiscreteTopology L] : DiscreteTopology L' := by
  let s : Set E := L
  let t : Set E := L'
  have hts : t ⊆ s := hle
  have hDs : DiscreteTopology s := by
    change DiscreteTopology L
    infer_instance
  exact DiscreteTopology.of_subset (s := s) (t := t) hDs hts

/-- Span of the first `s` vectors of a family `v : Fin m → L` (for `s ≤ m`). -/
def W (L : Submodule ℤ E) (m : ℕ) (v : Fin m → L) (s : ℕ) (hs : s ≤ m) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun j : Fin s => (v (Fin.castLE hs j) : E)))

/-- The full lattice points lying in `W s`, as a `ℤ`-submodule of `E`. -/
def Q (L : Submodule ℤ E) (m : ℕ) (v : Fin m → L) (s : ℕ) (hs : s ≤ m) : Submodule ℤ E :=
  L ⊓ (W L m v s hs).restrictScalars ℤ

lemma Q_le_L (L : Submodule ℤ E) (m : ℕ) (v : Fin m → L) (s : ℕ) (hs : s ≤ m) :
    Q L m v s hs ≤ L := by
  intro x hx
  exact (Submodule.mem_inf.mp hx).1

lemma Q_le_W_restrict (L : Submodule ℤ E) (m : ℕ) (v : Fin m → L) (s : ℕ) (hs : s ≤ m) :
    (Q L m v s hs : Submodule ℤ E) ≤ (W L m v s hs).restrictScalars ℤ := by
  intro x hx
  exact (Submodule.mem_inf.mp hx).2

/-- Membership of lattice elements of `Q s` in `W s`. -/
lemma Q_mem_W (L : Submodule ℤ E) (m : ℕ) (v : Fin m → L) (s : ℕ) (hs : s ≤ m)
    {x : E} (hx : x ∈ Q L m v s hs) : x ∈ W L m v s hs := by
  exact (Submodule.mem_inf.mp hx).2

/-- The first `s` vectors of the independent family are `ℝ`-independent. -/
lemma indep_prefix (L : Submodule ℤ E) (m : ℕ) (v : Fin m → L) (s : ℕ) (hs : s ≤ m)
    (hv : LinearIndependent ℝ (fun j : Fin m => (v j : E))) :
    LinearIndependent ℝ (fun j : Fin s => (v (Fin.castLE hs j) : E)) :=
  hv.comp (Fin.castLE hs) (Fin.castLE_injective hs)

lemma finrank_W (L : Submodule ℤ E) (m : ℕ) (v : Fin m → L) (s : ℕ) (hs : s ≤ m)
    (hv : LinearIndependent ℝ (fun j : Fin m => (v j : E))) :
    Module.finrank ℝ ↥(W L m v s hs) = s := by
  change Module.finrank ℝ ↥(Submodule.span ℝ (Set.range (fun j : Fin s =>
    (v (Fin.castLE hs j) : E)))) = s
  rw [finrank_span_eq_card (indep_prefix L m v s hs hv)]
  simp

lemma span_R_Q (L : Submodule ℤ E) (m : ℕ) (v : Fin m → L) (s : ℕ) (hs : s ≤ m) :
    span ℝ (Q L m v s hs : Set E) = W L m v s hs := by
  apply le_antisymm
  · exact span_le.mpr (by
      intro x hx
      exact (Submodule.mem_inf.mp hx).2)
  · exact span_le.mpr (by
      intro x hx
      rcases hx with ⟨j, rfl⟩
      have hxQ : (v (Fin.castLE hs j) : E) ∈ (Q L m v s hs : Set E) := by
        exact Submodule.mem_inf.mpr ⟨(v (Fin.castLE hs j)).2, subset_span ⟨j, rfl⟩⟩
      exact subset_span hxQ)

/-- The `ℤ`-rank of the lattice points inside `W s` is `s`. -/
lemma finrank_int_Q (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (m : ℕ) (v : Fin m → L) (s : ℕ) (hs : s ≤ m)
    (hv : LinearIndependent ℝ (fun j : Fin m => (v j : E))) :
    Module.finrank ℤ ↥(Q L m v s hs) = s := by
  classical
  let s0 : Set E := (Q L m v s hs : Set E)
  have hspan : span ℤ s0 = Q L m v s hs := by
    ext x
    simp [s0]
  have hdisc : DiscreteTopology ↥(span ℤ s0) := by
    apply discreteTopology_of_le_general (L := L) (L' := span ℤ s0)
    intro x hx
    have hxQ : x ∈ Q L m v s hs := by simpa [hspan] using hx
    exact (Submodule.mem_inf.mp hxQ).1
  have hreal : Set.finrank ℝ s0 = Set.finrank ℤ s0 :=
    Real.finrank_eq_int_finrank_of_discrete (s := s0) hdisc
  have hz : Set.finrank ℤ s0 = Module.finrank ℤ ↥(Q L m v s hs) := by
    dsimp [Set.finrank]
    exact (LinearEquiv.finrank_eq (LinearEquiv.ofEq (span ℤ s0) (Q L m v s hs) hspan))
  have hr : Set.finrank ℝ s0 = s := by
    dsimp [Set.finrank]
    exact (LinearEquiv.finrank_eq
      (LinearEquiv.ofEq (span ℝ s0) (W L m v s hs) (by simpa [s0] using span_R_Q L m v s hs))).trans
      (finrank_W L m v s hs hv)
  rw [← hz, ← hreal]
  exact hr

/-- `Q s` viewed as a submodule of the module `L`. -/
def Nsub (L : Submodule ℤ E) (m : ℕ) (v : Fin m → L) (s : ℕ) (hs : s ≤ m) : Submodule ℤ ↥L :=
  (Q L m v s hs).comap L.subtype

/-- The natural equivalence `Q s ≤ L ↪ Q s` used to move bases. -/
noncomputable def Nsub_equiv (L : Submodule ℤ E) (m : ℕ) (v : Fin m → L) (s : ℕ) (hs : s ≤ m) :
    ↥(Nsub L m v s hs) ≃ₗ[ℤ] ↥(Q L m v s hs) :=
  Submodule.comapSubtypeEquivOfLe (Q_le_L L m v s hs)

open Commons.Lattice.Module.basisExtensionPureRankHelpers

/-- A `ℤ`-basis of `Q s` indexed by `Fin s`. -/
noncomputable def Q_basis (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (m : ℕ) (v : Fin m → L) (s : ℕ) (hs : s ≤ m)
    (hv : LinearIndependent ℝ (fun j : Fin m => (v j : E))) :
    Module.Basis (Fin s) ℤ ↥(Q L m v s hs) := by
  classical
  let bL := Module.Free.chooseBasis ℤ ↥L
  obtain ⟨n, bN⟩ := Submodule.basisOfPid bL (Nsub L m v s hs)
  let e1 := submoduleToIntModuleEquiv (Nsub L m v s hs)
  let e2 := Nsub_equiv L m v s hs
  let bQ : Module.Basis (Fin n) ℤ ↥(Q L m v s hs) := (bN.map e1).map e2
  have hfin : Module.finrank ℤ ↥(Q L m v s hs) = n := by
    simpa using (Module.finrank_eq_card_basis bQ)
  have hfin' : Module.finrank ℤ ↥(Q L m v s hs) = s := finrank_int_Q L m v s hs hv
  have h : n = s := by omega
  exact bQ.reindex (finCongr h)

lemma W_mono (L : Submodule ℤ E) (m : ℕ) (v : Fin m → L) {s t : ℕ} (hs : s ≤ m) (ht : t ≤ m)
    (hst : s ≤ t) : W L m v s hs ≤ W L m v t ht := by
  exact Submodule.span_mono (by
    intro x hx
    rcases hx with ⟨j, rfl⟩
    refine ⟨Fin.castLE hst j, ?_⟩
    have hcast : Fin.castLE ht (Fin.castLE hst j) = Fin.castLE hs j := by
      apply Fin.ext
      simp
    simpa [hcast])

lemma Q_mono (L : Submodule ℤ E) (m : ℕ) (v : Fin m → L) {s t : ℕ} (hs : s ≤ m) (ht : t ≤ m)
    (hst : s ≤ t) : Q L m v s hs ≤ Q L m v t ht := by
  intro x hx
  exact Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).1,
    (W_mono L m v hs ht hst) (Submodule.mem_inf.mp hx).2⟩

lemma W_top (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (m : ℕ) (v : Fin m → L) (hm : Module.finrank ℤ L = m)
    (hv : LinearIndependent ℝ (fun j : Fin m => (v j : E))) :
    W L m v m (le_refl m) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq (K := ℝ)
  rw [finrank_W L m v m (le_refl m) hv, ← hm]
  exact ZLattice.rank ℝ L

lemma Q_top (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (m : ℕ) (v : Fin m → L) (hm : Module.finrank ℤ L = m)
    (hv : LinearIndependent ℝ (fun j : Fin m => (v j : E))) :
    Q L m v m (le_refl m) = L := by
  have hW : W L m v m (le_refl m) = ⊤ := W_top L m v hm hv
  calc
    Q L m v m (le_refl m) = L ⊓ (W L m v m (le_refl m)).restrictScalars ℤ := rfl
    _ = L ⊓ (⊤ : Submodule ℝ E).restrictScalars ℤ := by rw [hW]
    _ = L := by
      ext x
      simp

/-- Purity of `Q s` inside `Q (s+1)`, in the module sense needed by the extension lemma.
This holds because `W s` is a real vector subspace (closed under division by a nonzero integer). -/
lemma pure_Q (L : Submodule ℤ E) (m : ℕ) (v : Fin m → L) (t : ℕ) (ht : t ≤ m) (ht' : t + 1 ≤ m)
    (hle : Q L m v t ht ≤ Q L m v (t + 1) ht') :
    ∀ x : ↥(Q L m v (t + 1) ht'),
      (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ (Q L m v t ht).comap ((Q L m v (t + 1) ht').subtype)) →
        x ∈ (Q L m v t ht).comap ((Q L m v (t + 1) ht').subtype) := by
  intro x ha
  rcases ha with ⟨a, ha0, haN⟩
  have haxW : (a • (x : E)) ∈ W L m v t ht := by
    have hxQ : (a • (x : E)) ∈ Q L m v t ht := by
      simpa using haN
    exact Q_mem_W L m v t ht hxQ
  have hL : (x : E) ∈ L := by
    exact (Submodule.mem_inf.mp x.2).1
  have hcoeff : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
  have hxeq : (x : E) = (a : ℝ)⁻¹ • (a • (x : E)) := by
    rw [← Int.cast_smul_eq_zsmul ℝ a (x : E)]
    simp [hcoeff]
  have hxW : (x : E) ∈ W L m v t ht := by
    rw [hxeq]
    exact (W L m v t ht).smul_mem (a : ℝ)⁻¹ haxW
  exact (Submodule.mem_comap).mpr (Submodule.mem_inf.mpr ⟨hL, hxW⟩)

/-- One step of the chain construction: extend a basis of `Q t` with all elements lying in the
corresponding flag subspaces to a basis of `Q (t+1)` with the same property. -/
lemma chain_step (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (m : ℕ) (v : Fin m → L) (hv : LinearIndependent ℝ (fun j : Fin m => (v j : E)))
    (t : ℕ) (ht : t ≤ m) (ht' : t + 1 ≤ m)
    (β : Module.Basis (Fin t) ℤ ↥(Q L m v t ht))
    (hβ : ∀ j : Fin t, ((β j : ↥(Q L m v t ht)) : E) ∈ W L m v (j.val + 1) (by omega)) :
    ∃ γ : Module.Basis (Fin (t + 1)) ℤ ↥(Q L m v (t + 1) ht'),
      ∀ j : Fin (t + 1),
        ((γ j : ↥(Q L m v (t + 1) ht')) : E) ∈ W L m v (j.val + 1) (by omega) := by
  classical
  let M := ↥(Q L m v (t + 1) ht')
  let N : Submodule ℤ M := (Q L m v t ht).comap ((Q L m v (t + 1) ht').subtype)
  have hle : Q L m v t ht ≤ Q L m v (t + 1) ht' := Q_mono L m v ht ht' (Nat.le_succ t)
  let eN : ↥N ≃ₗ[ℤ] ↥(Q L m v t ht) := Submodule.comapSubtypeEquivOfLe hle
  let bN : Module.Basis (Fin t) ℤ ↥N := β.map eN.symm
  let bM : Module.Basis (Fin (t + 1)) ℤ M := Q_basis L m v (t + 1) ht' hv
  haveI : Module.Free ℤ M := Module.Free.of_basis bM
  haveI : Module.Finite ℤ M := Module.Finite.of_basis bM
  haveI : Module.Free ℤ ↥N := Module.Free.of_basis bN
  haveI : Module.Finite ℤ ↥N := Module.Finite.of_basis bN
  have hpureN : ∀ x : M, (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ N) → x ∈ N := by
    intro x ha
    apply pure_Q L m v t ht ht' hle
    exact ha
  obtain ⟨e, he⟩ := Commons.Lattice.Module.basis_extension_pure_rank
    (hd := Nat.le_succ t) (M := M) (N := N) bM bN hpureN
  refine ⟨e, ?_⟩
  intro j
  by_cases hj : j.val < t
  · let i : Fin t := ⟨j.val, hj⟩
    have hji : Fin.castLE (Nat.le_succ t) i = j := by
      apply Fin.ext
      rfl
    have hej : (e j : M) = (bN i : N) := by
      simpa [hji] using he i
    have hval : ((bN i : N) : E) = ((β i : ↥(Q L m v t ht)) : E) := by
      dsimp [bN, eN]
      rw [Submodule.comapSubtypeEquivOfLe_symm_apply]
    have hmem : ((β i : ↥(Q L m v t ht)) : E) ∈ W L m v (i.val + 1) (by omega) := hβ i
    simpa [hval, hji, hej] using hmem
  · have hjt : j.val = t := by omega
    have hjE : ((e j : M) : E) ∈ W L m v (j.val + 1) (by omega) := by
      have hQ : ((e j : M) : E) ∈ Q L m v (t + 1) ht' := (e j).2
      have hW : ((e j : M) : E) ∈ W L m v (t + 1) ht' := Q_mem_W L m v (t + 1) ht' hQ
      simpa [hjt] using hW
    exact hjE

/-- There exists a basis of the full lattice part `Q m = L` whose `j`-th element lies in the
span of the first `j+1` vectors `v`. -/
lemma chain_exists (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (m : ℕ) (hm : Module.finrank ℤ L = m) (v : Fin m → L)
    (hv : LinearIndependent ℝ (fun j : Fin m => (v j : E))) (hm1 : 1 ≤ m) :
    ∃ β : Module.Basis (Fin m) ℤ ↥(Q L m v m (le_refl m)),
      ∀ j : Fin m, ((β j : ↥(Q L m v m (le_refl m))) : E) ∈ W L m v (j.val + 1) (by omega) := by
  classical
  have hP : ∀ (t : ℕ) (ht : t ≤ m), 1 ≤ t →
      ∃ β : Module.Basis (Fin t) ℤ ↥(Q L m v t ht),
        ∀ j : Fin t, ((β j : ↥(Q L m v t ht)) : E) ∈ W L m v (j.val + 1) (by omega) := by
    intro t
    induction t with
    | zero =>
        intro ht h1
        omega
    | succ t ih =>
        intro ht' h1'
        by_cases ht0 : t = 0
        · subst t
          let β1 : Module.Basis (Fin 1) ℤ ↥(Q L m v 1 ht') := Q_basis L m v 1 ht' hv
          refine ⟨β1, ?_⟩
          intro j
          have hj0 : j.val = 0 := by omega
          have hQ : ((β1 j : ↥(Q L m v 1 ht')) : E) ∈ Q L m v 1 ht' := (β1 j).2
          have hW : ((β1 j : ↥(Q L m v 1 ht')) : E) ∈ W L m v 1 ht' := Q_mem_W L m v 1 ht' hQ
          simpa [hj0] using hW
        · have htle : t ≤ m := by omega
          have h1 : 1 ≤ t := by omega
          rcases ih htle h1 with ⟨β, hβ⟩
          obtain ⟨γ, hγ⟩ := chain_step L m v hv t htle ht' β hβ
          exact ⟨γ, hγ⟩
  rcases hP m (le_refl m) hm1 with ⟨βm, hβm⟩
  exact ⟨βm, hβm⟩

/-- `LinearEquiv.ofEq` preserves ambient values. -/
lemma ofEq_val_eqZ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q : Submodule ℤ E) (h : p = q) (x : ↥p) :
    (((LinearEquiv.ofEq p q h) x : ↥q) : E) = (x : E) := by
  subst h
  rfl

end flagBasis
open flagBasis

/-- Given `m` linearly independent lattice vectors `v`, there is a `ℤ`-basis `b` of the lattice
with the same flag of real spans. -/
theorem flag_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (m : ℕ) (hm : Module.finrank ℤ L = m) (v : Fin m → L)
    (hv : LinearIndependent ℝ (fun j : Fin m => (v j : E))) :
    ∃ b : Module.Basis (Fin m) ℤ L,
      ∀ k : Fin m,
        Submodule.span ℝ (Set.range (fun j : Fin (k.val + 1) =>
          ((b ⟨j.val, by omega⟩ : L) : E))) =
        Submodule.span ℝ (Set.range (fun j : Fin (k.val + 1) =>
          ((v ⟨j.val, by omega⟩ : L) : E))) := by
  classical
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  by_cases hm0 : m = 0
  · -- rank zero: trivial
    have hfin : Module.finrank ℤ L = 0 := by simpa [hm0] using hm
    let b : Module.Basis (Fin m) ℤ L := Module.finBasisOfFinrankEq ℤ L (by simpa [hm0] using hfin)
    refine ⟨b, ?_⟩
    intro k
    exfalso
    have hk : k.val < 0 := by simpa [hm0] using k.isLt
    exact (Nat.not_lt_zero k.val) hk
  · -- m ≥ 1
    have hm1 : 1 ≤ m := by omega
    obtain ⟨βm, hβm⟩ := flagBasis.chain_exists L m hm v hv hm1
    have hQtop : Q L m v m (le_refl m) = L := flagBasis.Q_top L m v hm hv
    let eQ : ↥(Q L m v m (le_refl m)) ≃ₗ[ℤ] L := LinearEquiv.ofEq (Q L m v m (le_refl m)) L hQtop
    let b : Module.Basis (Fin m) ℤ L := βm.map eQ
    refine ⟨b, ?_⟩
    intro k
    let s : ℕ := k.val + 1
    have hs : s ≤ m := by omega
    -- images of a Z-basis of L give an R-basis of E
    have hbE : LinearIndependent ℝ (fun j : Fin m => (b j : E)) := by
      have hbE' : LinearIndependent ℝ (fun j : Fin m => ((b.ofZLatticeBasis ℝ L j) : E)) :=
        (b.ofZLatticeBasis ℝ L).linearIndependent
      simpa using hbE'
    have hβb : ∀ j : Fin m, ((b j : L) : E) = ((βm j : ↥(Q L m v m (le_refl m))) : E) := by
      intro j
      change (((βm.map eQ) j : ↥L) : E) = ((βm j : ↥(Q L m v m (le_refl m))) : E)
      rw [Basis.map_apply]
      exact ofEq_val_eqZ (Q L m v m (le_refl m)) L hQtop (βm j)
    have hindβm : LinearIndependent ℝ (fun j : Fin m =>
        ((βm j : ↥(Q L m v m (le_refl m))) : E)) := by
      convert hbE using 1
      ext j
      exact (hβb j).symm
    have hindβs : LinearIndependent ℝ (fun j : Fin s =>
        ((βm (Fin.castLE hs j) : ↥(Q L m v m (le_refl m))) : E)) :=
      hindβm.comp (Fin.castLE hs) (Fin.castLE_injective hs)
    -- βm-prefix span is contained in W s
    have hleβ : Submodule.span ℝ (Set.range (fun j : Fin s =>
          ((βm (Fin.castLE hs j) : ↥(Q L m v m (le_refl m))) : E))) ≤ W L m v s hs := by
      refine span_le.mpr ?_
      rintro x ⟨j, rfl⟩
      have hWj : ((βm (Fin.castLE hs j) : ↥(Q L m v m (le_refl m))) : E) ∈
          W L m v (j.val + 1) (by omega) := hβm (Fin.castLE hs j)
      exact W_mono L m v (by omega) hs (by omega) hWj
    have hdimW : Module.finrank ℝ ↥(W L m v s hs) = s := flagBasis.finrank_W L m v s hs hv
    have hdimβ : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range (fun j : Fin s =>
          ((βm (Fin.castLE hs j) : ↥(Q L m v m (le_refl m))) : E)))) = s := by
      rw [finrank_span_eq_card hindβs]
      simp
    have heqβ : Submodule.span ℝ (Set.range (fun j : Fin s =>
          ((βm (Fin.castLE hs j) : ↥(Q L m v m (le_refl m))) : E))) = W L m v s hs := by
      exact Submodule.eq_of_le_of_finrank_le hleβ (by rw [hdimW, hdimβ])
    -- b-prefix span equals βm-prefix span (pointwise equal values)
    have heqB : Submodule.span ℝ (Set.range (fun j : Fin s =>
          ((b (Fin.castLE hs j) : L) : E))) =
        Submodule.span ℝ (Set.range (fun j : Fin s =>
          ((βm (Fin.castLE hs j) : ↥(Q L m v m (le_refl m))) : E))) := by
      apply congrArg (Submodule.span ℝ)
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        refine ⟨j, ?_⟩
        exact hβb (Fin.castLE hs j)
      · rintro ⟨j, rfl⟩
        refine ⟨j, ?_⟩
        exact (hβb (Fin.castLE hs j)).symm
    -- assemble: statement LHS = b-castLE span = βm-castLE span = W = v-castLE span = statement RHS
    calc
      Submodule.span ℝ (Set.range (fun j : Fin s => ((b ⟨j.val, by omega⟩ : L) : E)))
          = Submodule.span ℝ (Set.range (fun j : Fin s => ((b (Fin.castLE hs j) : L) : E))) := by rfl
      _ = W L m v s hs := by rw [heqB, heqβ]
      _ = Submodule.span ℝ (Set.range (fun j : Fin s =>
          ((v (Fin.castLE hs j) : L) : E))) := by rfl
      _ = Submodule.span ℝ (Set.range (fun j : Fin s => ((v ⟨j.val, by omega⟩ : L) : E))) := by rfl

end Commons.Lattice.Minkowski