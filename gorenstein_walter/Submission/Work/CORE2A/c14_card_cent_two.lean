import Mathlib
import Submission.Work.CORE2A.TorusDefs

/-!
# CORE2A: `c14_card_cent_two`

Let `N ≤ M ≤ G` be subgroups of a finite group `G` with `[M : N] = 2`, and let `t ∈ G` be an
element whose `M`-conjugacy class is already realised inside `N` (hypothesis `hcl`).  Then the
`M`-centralizer of `t` is exactly twice the `N`-centralizer of `t`:

`|C_M(t)| = 2 * |C_N(t)|`.

The argument is orbit–stabilizer.  Since `N ≤ M` and every `M`-conjugate of `t` is an
`N`-conjugate, the two conjugation orbits coincide, so

`|M| / |C_M(t)| = |M·t| = |N·t| = |N| / |C_N(t)|`,

and the conclusion follows from `|M| = 2 * |N|` (`N.relIndex M = 2`).
-/

namespace Work.CORE2A

open Subgroup

/-- Orbit–stabilizer theorem, in `Nat.card` form. -/
private theorem nat_card_orbit_mul_card_stabilizer {Gr X : Type*} [Group Gr] [MulAction Gr X]
    (x : X) :
    Nat.card Gr = Nat.card (MulAction.orbit Gr x) * Nat.card (MulAction.stabilizer Gr x) := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Gr x)).symm

/-- For the conjugation action of a subgroup `M` on the ambient group `G`, encoded by
`hsmul`, the stabilizer of `t` is `M ⊓ C_G(t)`. -/
private noncomputable def conjStabEquiv {G : Type} [Group G] (M : Subgroup G) (t : G)
    [MulAction ↥M G] (hsmul : ∀ (m : ↥M) (x : G), m • x = (m : G) * x * (m : G)⁻¹) :
    MulAction.stabilizer ↥M t ≃ ↥(M ⊓ Subgroup.centralizer ({t} : Set G)) where
  toFun x := ⟨(x.1 : G), by
    refine ⟨x.1.2, ?_⟩
    change (x.1 : G) ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : (x.1 : G) * t * (x.1 : G)⁻¹ = t := by
      rw [← hsmul x.1 t]; exact x.2
    calc (x.1 : G) * t = ((x.1 : G) * t * (x.1 : G)⁻¹) * (x.1 : G) := by group
      _ = t * (x.1 : G) := by rw [h]⟩
  invFun y := ⟨⟨(y.1 : G), y.2.1⟩, by
    rw [MulAction.mem_stabilizer_iff]
    rw [hsmul]
    change (y.1 : G) * t * (y.1 : G)⁻¹ = t
    have h : (y.1 : G) * t = t * (y.1 : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp y.2.2
    rw [h]; group⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl

theorem c14_card_cent_two {G : Type} [Group G] [Finite G] {N M : Subgroup G} (t : G) (hNM : N ≤ M) (h2 : N.relIndex M = 2) (hcl : ∀ m ∈ M, ∃ n ∈ N, m * t * m⁻¹ = n * t * n⁻¹) : Nat.card ↥(M ⊓ Subgroup.centralizer ({t} : Set G)) = 2 * Nat.card ↥(N ⊓ Subgroup.centralizer ({t} : Set G)) := by
  letI actM : MulAction ↥M G :=
    MulAction.compHom (M := ConjAct G) (N := ↥M) G (ConjAct.toConjAct.toMonoidHom.comp M.subtype)
  letI actN : MulAction ↥N G :=
    MulAction.compHom (M := ConjAct G) (N := ↥N) G (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
  have hsmulM : ∀ (m : ↥M) (x : G), m • x = (m : G) * x * (m : G)⁻¹ := by
    intro m x
    rw [MulAction.compHom_smul_def]
    show ConjAct.toConjAct (M.subtype m) • x = (m : G) * x * (m : G)⁻¹
    rw [ConjAct.toConjAct_smul_eq_mulAut_conj, MulAut.conj_apply]
    rfl
  have hsmulN : ∀ (n : ↥N) (x : G), n • x = (n : G) * x * (n : G)⁻¹ := by
    intro n x
    rw [MulAction.compHom_smul_def]
    show ConjAct.toConjAct (N.subtype n) • x = (n : G) * x * (n : G)⁻¹
    rw [ConjAct.toConjAct_smul_eq_mulAut_conj, MulAut.conj_apply]
    rfl
  -- `|M| = 2 * |N|`
  have hMN : Nat.card ↥M = 2 * Nat.card ↥N := by
    have h := Subgroup.relIndex_mul_card N M
    rw [h2, inf_eq_left.mpr hNM] at h
    exact h.symm
  -- orbit–stabilizer for the two conjugation actions
  have hMs := nat_card_orbit_mul_card_stabilizer (Gr := ↥M) (X := G) t
  have hNs := nat_card_orbit_mul_card_stabilizer (Gr := ↥N) (X := G) t
  have hstabM : Nat.card (MulAction.stabilizer ↥M t)
      = Nat.card ↥(M ⊓ Subgroup.centralizer ({t} : Set G)) :=
    Nat.card_congr (conjStabEquiv M t hsmulM)
  have hstabN : Nat.card (MulAction.stabilizer ↥N t)
      = Nat.card ↥(N ⊓ Subgroup.centralizer ({t} : Set G)) :=
    Nat.card_congr (conjStabEquiv N t hsmulN)
  rw [hstabM] at hMs
  rw [hstabN] at hNs
  -- the two conjugation orbits coincide
  have horbit : MulAction.orbit ↥M t = MulAction.orbit ↥N t := by
    ext x
    simp only [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨m, hm⟩
      obtain ⟨n, hnN, hn⟩ := hcl (m : G) m.2
      refine ⟨⟨n, hnN⟩, ?_⟩
      rw [hsmulN]
      change n * t * n⁻¹ = x
      rw [← hn, ← hsmulM m t, hm]
    · rintro ⟨n, hn⟩
      refine ⟨⟨(n : G), hNM n.2⟩, ?_⟩
      rw [hsmulM]
      change (n : G) * t * (n : G)⁻¹ = x
      rw [← hsmulN n t, hn]
  rw [← horbit] at hNs
  -- cancel the common orbit size
  have ht : t ∈ MulAction.orbit ↥M t := MulAction.mem_orbit_iff.mpr ⟨1, one_smul ↥M t⟩
  have ho : 0 < Nat.card (MulAction.orbit ↥M t) := by
    haveI : Nonempty ↥(MulAction.orbit ↥M t) := ⟨⟨t, ht⟩⟩
    exact Nat.card_pos
  have key : Nat.card (MulAction.orbit ↥M t)
        * Nat.card ↥(M ⊓ Subgroup.centralizer ({t} : Set G))
      = Nat.card (MulAction.orbit ↥M t)
        * (2 * Nat.card ↥(N ⊓ Subgroup.centralizer ({t} : Set G))) := by
    rw [← hMs, hMN, hNs]
    ring
  exact Nat.mul_left_cancel ho key

end Work.CORE2A
