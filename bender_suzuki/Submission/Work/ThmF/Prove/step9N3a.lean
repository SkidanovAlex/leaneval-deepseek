import Mathlib
import Submission.Work.ThmF.ChV3.Chain15
import Submission.Work.Frobenius.Complement.isPGroup_isCyclic_of_no_basicGroup
import Submission.Work.Frobenius.Complement.sylow_isCyclic_of_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step9N3a` — a `p`-subgroup of `W` is cyclic

Peterfalvi II Ch. V §3, step (9), input **N3a** (see
`Submission/Work/NOTES_LEAD_bs_pass13.md` §3).  Let `p = |P|` be an odd prime, `Q` a complement
of `D = H ⊓ H^t` in `H`, `V = C_D(t)`, `W = C_V(K)`, and `Q₁ = O_{2'}(Q) = oddPart Q`.  If `T ≤ W`
is a `p`-group normalising `Q₁` and every `w ∈ W`, `w ≠ 1`, centralises no non-trivial element of
`Q₁` (`hfpfW`), then `T` is cyclic.

The argument is Burnside's criterion: a finite `p`-group of *odd* order with no subgroup
isomorphic to `C_p × C_p` is cyclic
(`Work.Frobenius.Complement.isPGroup_isCyclic_of_no_basicGroup`).  So suppose `E ≤ T` with
`E ≅ C_p × C_p`.  As `T ≤ N_G(Q₁)`, conjugation endows `Q₁` with an action of `E`
(`Subgroup.normalizerMonoidHom`).  It is fixed-point-free: if `e ∈ E#` fixes `n ∈ Q₁`, then
`n ∈ Q₁ ⊓ C_G(e) = ⊥` by `hfpfW`.  Since `E` is an abelian `p`-group acting fixed-point-freely on
the non-trivial group `Q₁`, the theorem `isPGroup_abelian_fpf_isCyclic` forces `E` to be cyclic,
contradicting that `C_p × C_p` is not cyclic
(`Work.Frobenius.Complement.not_isCyclic_multiplicative_zmod_prod`).
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ThmF.Prove

theorem step9N3a {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {P T : Subgroup G}
    (hp : (Nat.card P).Prime) (hp2 : Nat.card P ≠ 2) (hTW : T ≤ Work.ThmF.W H t)
    (hTp : IsPGroup (Nat.card P) T) (hQ1 : Work.ThmF.oddPart Q ≠ ⊥)
    (hpQ1 : ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.oddPart Q))
    (hTQ : T ≤ Subgroup.normalizer (Work.ThmF.oddPart Q : Set G))
    (hfpfW : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → Work.ThmF.oddPart Q ⊓ Subgroup.centralizer ({w} : Set G) = ⊥) :
    IsCyclic ↥T := by
  -- Burnside: it suffices to exclude a subgroup `Q0 ≤ T` isomorphic to `C_p × C_p`.
  refine Work.Frobenius.Complement.isPGroup_isCyclic_of_no_basicGroup hp hp2 hTp ?_
  rintro Q0 ⟨e⟩
  have hEp : IsPGroup (Nat.card P) ↥Q0 := hTp.to_subgroup Q0
  haveI : IsMulCommutative ↥Q0 :=
    isMulCommutative_iff.mpr (fun a b => e.injective (by rw [map_mul, map_mul, mul_comm]))
  haveI : Nontrivial ↥(Work.ThmF.oddPart Q) := (Subgroup.nontrivial_iff_ne_bot _).mpr hQ1
  -- the conjugation action of `Q0` on `Q₁ = oddPart Q`
  let g : ↥Q0 →* ↥(Subgroup.normalizer (Work.ThmF.oddPart Q : Set G)) :=
  { toFun := fun a => ⟨((a : ↥T) : G), hTQ (a : ↥T).2⟩
    map_one' := Subtype.ext rfl
    map_mul' := fun a b => Subtype.ext rfl }
  let rho : ↥Q0 →* MulAut ↥(Work.ThmF.oddPart Q) :=
    (Subgroup.normalizerMonoidHom (Work.ThmF.oddPart Q)).comp g
  -- `Q0` is abelian and acts fixed-point-freely, hence is cyclic: contradiction.
  have hcyc : IsCyclic ↥Q0 :=
    Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic hp hEp rho (fun a ha n hn => by
      have h1 : ((rho a) n : G) = ((a : ↥T) : G) * (n : G) * (((a : ↥T) : G))⁻¹ := rfl
      have h2 : ((a : ↥T) : G) * (n : G) * (((a : ↥T) : G))⁻¹ = (n : G) := by
        rw [← h1]; exact congrArg Subtype.val hn
      have hcomm : ((a : ↥T) : G) * (n : G) = (n : G) * ((a : ↥T) : G) :=
        (mul_inv_eq_iff_eq_mul).mp h2
      have hmem : (n : G) ∈
          Work.ThmF.oddPart Q ⊓ Subgroup.centralizer ({((a : ↥T) : G)} : Set G) :=
        Subgroup.mem_inf.mpr ⟨n.2, Subgroup.mem_centralizer_iff.mpr (fun y hy => by
          rw [Set.mem_singleton_iff] at hy; subst hy; exact hcomm)⟩
      have hbot := hfpfW ((a : ↥T) : G) (hTW (a : ↥T).2)
        (fun h => ha (Subtype.ext (Subtype.ext (by simpa using h))))
      rw [hbot] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem))
  have hcyc' : IsCyclic (Multiplicative (ZMod (Nat.card P) × ZMod (Nat.card P))) :=
    (MulEquiv.isCyclic e).mp hcyc
  exact Work.Frobenius.Complement.not_isCyclic_multiplicative_zmod_prod hp hcyc'

end Work.ThmF.Prove
