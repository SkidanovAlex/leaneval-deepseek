import Mathlib
import Submission.Work.BW.BWGradedBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.BW

/-- If an `B`-module `M ⧸ N` is annihilated by an ideal `I`, then the lattice of
`B`-submodules of `M ⧸ N` embeds order-theoretically into the lattice of
`B ⧸ I`-submodules (both have the very same carrier sets).  This lets one transfer
`IsArtinian`/`IsNoetherian` from the quotient-ring module structure down to the
original one. -/
noncomputable def torsionQuotOrderEmbedding {B : Type*} [CommRing B] {M : Type*}
    [AddCommGroup M] [Module B M] (N : Submodule B M) (I : Ideal B)
    (hTB : Module.IsTorsionBySet B (M ⧸ N) (I : Set B)) :
    letI := hTB.module
    Submodule B (M ⧸ N) ↪o Submodule (B ⧸ I) (M ⧸ N) := by
  letI := hTB.module
  refine OrderEmbedding.ofMapLEIff
    (fun V : Submodule B (M ⧸ N) =>
      { carrier := (V : Set (M ⧸ N))
        zero_mem' := V.zero_mem
        add_mem' := fun hx hy => V.add_mem hx hy
        smul_mem' := fun c x hx => ?_ }) ?_
  · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Module.IsTorsionBySet.mk_smul hTB b x]
    exact V.smul_mem b hx
  · intro V W
    exact Iff.rfl

/-- **A finitely generated module modulo a cyclic submodule with torsion quotient has finite length.**

Let `𝔭` be a prime ideal of a commutative ring `B`, `M` a finitely generated `B`-module annihilated
by `𝔭`, `m₀ ∈ M`, and assume

* every element of `M` becomes a multiple of `m₀` after multiplication by some `d ∉ 𝔭`
  (`htor`: the quotient `M ⧸ B·m₀` is `𝔭`-torsion),
* for every `r ∉ 𝔭` the quotient ring `B ⧸ (𝔭 + (r))` is Artinian (`hart`).

Then `M ⧸ B·m₀` has finite length over `B`.

Route. `T := M ⧸ B·m₀` is finitely generated (`hfg`) and, by `htor`, every element of `T` is killed
by some `d ∉ 𝔭`. Choosing finitely many generators `t₁, …, tₙ` of `T`, the product `d` of the
corresponding elements is not in `𝔭` (`𝔭` is prime) and kills `T`, so `T` is a module over
`B ⧸ (𝔭 + (d))`, which is Artinian by `hart`. A finitely generated module over an Artinian ring is
Artinian (`isArtinian_of_fg_of_artinian`), and together with Noetherianness of `T` (finitely
generated over the Artinian, hence Noetherian, ring `B ⧸ (𝔭 + (d))`) this gives
`IsFiniteLength` (`isFiniteLength_iff_isNoetherian_isArtinian`). -/
theorem isFiniteLength_quot_span_of_torsion {B : Type*} [CommRing B]
    (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime) {M : Type*} [AddCommGroup M] [Module B M]
    (m₀ : M) (hann : ∀ b ∈ 𝔭, ∀ m : M, b • m = 0) (hfg : Module.Finite B M)
    (htor : ∀ m : M, ∃ d : B, d ∉ 𝔭 ∧ d • m ∈ Submodule.span B {m₀})
    (hart : ∀ r : B, r ∉ 𝔭 → IsArtinianRing (B ⧸ (𝔭 ⊔ Ideal.span {r}))) :
    IsFiniteLength B (M ⧸ (Submodule.span B {m₀})) := by
  classical
  set N : Submodule B M := Submodule.span B {m₀} with hN
  have hfgT : Module.Finite B (M ⧸ N) := by
    haveI : Module.Finite B M := hfg
    exact Module.Finite.quotient B N
  haveI := hfgT
  -- every element of the quotient is killed by something outside `𝔭`
  have hkill : ∀ t : M ⧸ N, ∃ d : B, d ∉ 𝔭 ∧ d • t = 0 := by
    intro t
    obtain ⟨m, rfl⟩ := N.mkQ_surjective t
    obtain ⟨d, hd, hdm⟩ := htor m
    exact ⟨d, hd, by
      rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul (p := N), Submodule.Quotient.mk_eq_zero]
      exact hdm⟩
  -- finitely many generators, and the product of the associated multipliers
  obtain ⟨S, hS⟩ := hfgT.fg_top
  choose dd hdd using hkill
  set d : B := ∏ t ∈ S, dd t with hdform
  have hd_notmem : d ∉ 𝔭 := by
    intro hd
    rw [hdform, Ideal.IsPrime.prod_mem_iff] at hd
    obtain ⟨t, -, ht⟩ := hd
    exact (hdd t).1 ht
  have hd_kill : ∀ t ∈ S, d • t = 0 := by
    intro t htS
    rw [hdform, ← Finset.prod_erase_mul S dd htS, mul_smul, (hdd t).2, smul_zero]
  have hd_kill_all : ∀ x : M ⧸ N, d • x = 0 := by
    intro x
    have hx : x ∈ Submodule.span B (↑S : Set (M ⧸ N)) := by rw [hS]; trivial
    exact Submodule.span_induction (p := fun x _ => d • x = 0)
      (fun y hy => hd_kill y hy)
      (by simp)
      (fun y z _ _ ihy ihz => by rw [smul_add, ihy, ihz, add_zero])
      (fun a y _ ihy => by rw [smul_comm, ihy, smul_zero])
      hx
  -- `𝔭` annihilates the quotient
  have hannT : 𝔭 ≤ Module.annihilator B (M ⧸ N) := by
    intro b hb
    rw [Module.mem_annihilator]
    intro t
    obtain ⟨m, rfl⟩ := N.mkQ_surjective t
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul (p := N), Submodule.Quotient.mk_eq_zero]
    rw [hann b hb m]
    exact N.zero_mem
  have hd_ann : d ∈ Module.annihilator B (M ⧸ N) := by
    rw [Module.mem_annihilator]
    exact hd_kill_all
  -- the quotient is a module over the Artinian ring `B ⧸ (𝔭 + (d))`
  set I : Ideal B := 𝔭 ⊔ Ideal.span {d} with hIdef
  have hI_le : I ≤ Module.annihilator B (M ⧸ N) := by
    rw [hIdef]
    exact sup_le hannT (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hd_ann))
  have hTB : Module.IsTorsionBySet B (M ⧸ N) (I : Set B) :=
    (Module.isTorsionBySet_iff_subset_annihilator B (M ⧸ N)).mpr hI_le
  letI : Module (B ⧸ I) (M ⧸ N) := hTB.module
  haveI : IsArtinianRing (B ⧸ I) := by rw [hIdef]; exact hart d hd_notmem
  have hfgS : Module.Finite (B ⧸ I) (M ⧸ N) :=
    Module.Finite.of_surjective hTB.semilinearMap Function.surjective_id
  have hFLS : IsFiniteLength (B ⧸ I) (M ⧸ N) :=
    ((IsArtinianRing.tfae (B ⧸ I) (M ⧸ N)).out 1 4).mp hfgS
  have hNoeS : IsNoetherian (B ⧸ I) (M ⧸ N) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hFLS).1
  have hArtS : IsArtinian (B ⧸ I) (M ⧸ N) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hFLS).2
  -- transport Noetherian/Artinian back along the order embedding
  have e := torsionQuotOrderEmbedding N I hTB
  have hArtB : IsArtinian B (M ⧸ N) := by
    letI : WellFoundedLT (Submodule (B ⧸ I) (M ⧸ N)) := hArtS
    exact e.wellFoundedLT
  have hNoeB : IsNoetherian B (M ⧸ N) := by
    rw [isNoetherian_iff]
    haveI : IsNoetherian (B ⧸ I) (M ⧸ N) := hNoeS
    exact e.wellFoundedGT
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨hNoeB, hArtB⟩

end Work.BW
