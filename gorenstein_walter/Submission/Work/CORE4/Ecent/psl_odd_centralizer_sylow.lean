import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.RED.DihedralFacts
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic

namespace Work.CORE4.Ecent

/-- In `L₂(q)` (`q = p^k`, `p` odd, `q ≥ 5`), an element of odd order centralising a Sylow
2-subgroup is trivial.

`Work.GW2.L2SylowDihedralProp` and `Work.GW2.L2FourGroupProp` are the fields
`I.toolkit.l2syl` / `I.toolkit.l2four` of the input bundle of area CORE4
(`Submission.Work.CORE4.Defs`); `PSL(2, F) = Matrix.ProjectiveSpecialLinearGroup (Fin 2) F`.

Proof plan: `hsyl` gives `↥D ≃* DihedralGroup n` with `2 ≤ n`; `↥D` is a 2-group, so
`|D| = 2 * n` (`DihedralGroup.nat_card`) is a power of `2`, whence `n` is even and nonzero
(direct arithmetic from `IsPGroup.iff_card`; alternatively
`Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic`, which additionally needs
non-cyclicity of `↥D`).  `Work.RED.DihedralFacts.fourGroup_exists_of_even` (a field of
`Work.RED.GW2.DihedralFactsProp`, proved as `Work.RED.DihedralFacts`; note
`Work.RED.GW2.IsFourGroup` is definitionally `Work.GW2.IsFourGroup`) gives a Klein four-group
inside `DihedralGroup n`; pulling it back along the isomorphism, then pushing it along
`↥D ↪ L₂(q)`, gives a four-group `V ≤ D ≤ L₂(q)`.  By `hfour` (`Work.GW2.L2FourGroupProp`)
`C_{L₂(q)}(V) = V`, so `x ∈ C(D) ≤ C(V) = V` lies in a 2-group; with `orderOf x` odd (and
`orderOf x ∣ |V| = 4`) this forces `x = 1`. -/
theorem psl_odd_centralizer_sylow (p k : ℕ) [Fact p.Prime] (hp : Odd p)
    (hq : 5 ≤ p ^ k) (hsyl : Work.GW2.L2SylowDihedralProp) (hfour : Work.GW2.L2FourGroupProp)
    (D : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))
    {x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)} (hxodd : Odd (orderOf x))
    (hc : x ∈ Subgroup.centralizer
      ((D : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))) :
    x = 1 := by
  -- `D` is dihedral: `↥D ≃* DihedralGroup n` with `2 ≤ n`.
  obtain ⟨n, hn2, ⟨e⟩⟩ := hsyl p k hp hq D
  -- `↥D` is a 2-group, so `2 * n = |DihedralGroup n| = |D| = 2 ^ m`.
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := ↥D)).1 D.isPGroup'
  have hpow : 2 * n = 2 ^ m := by
    rw [← DihedralGroup.nat_card, ← Nat.card_congr e.toEquiv]
    exact hm
  have hm1 : 1 ≤ m := by
    rcases m with _ | m
    · rw [pow_zero] at hpow; omega
    · omega
  have hpow' : 2 ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
  have hn_eq : n = 2 ^ (m - 1) :=
    Nat.mul_left_cancel (by norm_num : 0 < 2) (by rw [hpow, hpow'])
  -- hence `n` is even (and nonzero, from `2 ≤ n`).
  have heven : Even n := by
    rw [hn_eq]
    rcases Nat.eq_zero_or_pos (m - 1) with h | h
    · rw [h, pow_zero] at hn_eq; omega
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m - 1 ≠ 0)
      rw [hj, pow_succ']
      exact ⟨2 ^ j, by ring⟩
  -- a Klein four-group inside `DihedralGroup n`, pulled back to `↥D` and pushed into `L₂(q)`.
  obtain ⟨V₀, hV₀⟩ :=
    @Work.RED.DihedralFacts.fourGroup_exists_of_even n ⟨by omega⟩ heven
  have hV4 : Work.RED.GW2.IsFourGroup (V₀.map (e.symm : DihedralGroup n ≃* ↥D).toMonoidHom) :=
    (Work.RED.GW2.isFourGroup_map_iff e.symm V₀).2 hV₀
  set W : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    (V₀.map (e.symm : DihedralGroup n ≃* ↥D).toMonoidHom).map
      (D : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))).subtype
    with hWdef
  have hWsq : ∀ w ∈ W, w ^ 2 = 1 := by
    intro w hw
    rw [hWdef] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [← map_pow, hV4.2 v hv, map_one]
  have hWcard : Nat.card ↥W = 4 := by
    rw [hWdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hV4.1]
  have hW4 : Work.GW2.IsFourGroup W := ⟨hWcard, hWsq⟩
  have hWD : W ≤ (D : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := by
    rw [hWdef]
    rintro g ⟨v, _hv, rfl⟩
    exact v.2
  -- `W` is self-centralizing in `L₂(q)`.
  have hcen : Subgroup.centralizer
      (W : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) = W :=
    (hfour p k hp hq).1 W hW4
  -- so `x ∈ C(D) ≤ C(W) = W`.
  have hxW : x ∈ W := by
    rw [← hcen, Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_iff.1 hc g (hWD hg)
  have hx2 : x ^ 2 = 1 := hWsq x hxW
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 hx2
  -- `orderOf x` is a divisor of `2` and odd, so it is `1`.
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hxodd
    obtain ⟨t, ht⟩ := hxodd
    omega

end Work.CORE4.Ecent
