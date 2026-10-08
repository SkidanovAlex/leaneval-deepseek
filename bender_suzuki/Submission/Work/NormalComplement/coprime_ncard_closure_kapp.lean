import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.appI_five_a

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

theorem coprime_ncard_closure_kapp {G : Type*} [Group G] [Finite G]
    {d : ℕ} (hd : d.Prime) {t : G} (ht : orderOf t = d) {X : Subgroup G}
    (htX : Work.NormalComplement.NormalizedBy t X) (hdX : Nat.Coprime (Nat.card X) d)
    (hsolv : Group.IsSolvable X)
    (hcop : Nat.Coprime (Work.NormalComplement.Kapp t X).ncard
      (Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({t} : Set G) ⊓ X)))) :
    Nat.Coprime (Nat.card ↥(Subgroup.closure (Work.NormalComplement.Kapp t X)))
      (Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({t} : Set G) ⊓ X))) := by
  -- App. I (5)(a): a prime divides `|⟨K⟩|` iff it divides `|K|`.
  have hiff := appI_five_a hd ht htX hdX hsolv
  -- Coprimality is equivalent to the non-existence of a common prime divisor.
  by_contra h
  obtain ⟨p, hp, hpa, hpN⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  -- `p ∣ |⟨K⟩|` implies `p ∣ |K|`, contradicting `Nat.Coprime |K| |F|`.
  have hpb : p ∣ (Kapp t X).ncard := (hiff p hp).mp hpa
  exact absurd hcop (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpb, hpN⟩)

end Work.NormalComplement
