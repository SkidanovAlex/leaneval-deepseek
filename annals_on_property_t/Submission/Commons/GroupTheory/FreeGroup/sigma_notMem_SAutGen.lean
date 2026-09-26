import Submission.Commons.GroupTheory.FreeGroup.abHom_mk_toAdd
import Submission.Commons.GroupTheory.FreeGroup.sigma_conj_mem_SAutGen

set_option autoImplicit false

namespace Commons.GroupTheory.FreeGroup

/-!
# `σᵢ` is not a Nielsen transvection

The single-generator inversion `σᵢ` (`a_u ↦ a_u` for `u ≠ i`, `a_i ↦ a_i⁻¹`) is
**not** one of the Nielsen transvections generating `SAut(F_n)`.

The proof is a one-coordinate abelianisation argument.  Write `abHom n` for the
abelianisation `F_n → ℤ^n` already in the commons (the `v`-th coordinate of
`abHom n x` is the exponent sum of the letter `v` in `x`).  Suppose
`sAutAut p = σᵢ` with `p = ⟨((u,v),(b,e)), huv⟩`, and evaluate the `v`-th
coordinate at the generator `a_u`:

* every Nielsen transvection moves `a_u ↦ a_u · a_v^{±1}` or
  `a_v^{±1} · a_u`, so this coordinate is `±1 ≠ 0`;
* `σᵢ` fixes `a_u` or inverts it according to whether `u = i`, so the
  exponent sum of `a_v` (with `v ≠ u`) in it is `0`.

Contradiction.  (The definitions of the Nielsen transvections, the inversions
and `SAutGen` live in the commons module
`Submission.Commons.GroupTheory.FreeGroup.sigma_conj_mem_SAutGen`, which this
file imports; they are verbatim copies of the development's own definitions, so
this lemma applies to those as well by definitional equality.)
-/

private lemma abHom_of_toAdd (n : ℕ) (j k : Fin n) :
    ((abHom n) (FreeGroup.of j)).toAdd k = if k = j then 1 else 0 := by
  rw [abHom, FreeGroup.lift_apply_of, toAdd_ofAdd, Pi.single_apply]

private lemma abHom_rho_toAdd (n : ℕ) (u v : Fin n) (huv : u ≠ v) :
    ((abHom n) ((rho u v huv) (a u))).toAdd v = 1 := by
  rw [rho_apply_self, MonoidHom.map_mul, toAdd_mul, Pi.add_apply, abHom_of_toAdd n u v,
    abHom_of_toAdd n v v, if_neg (fun h : v = u => huv h.symm), if_pos rfl]
  norm_num

private lemma abHom_rhoNeg_toAdd (n : ℕ) (u v : Fin n) (huv : u ≠ v) :
    ((abHom n) ((rhoNeg u v huv) (a u))).toAdd v = -1 := by
  rw [rhoNeg_apply_self, MonoidHom.map_mul, MonoidHom.map_inv, toAdd_mul, toAdd_inv,
    Pi.add_apply, Pi.neg_apply, abHom_of_toAdd n u v, abHom_of_toAdd n v v,
    if_neg (fun h : v = u => huv h.symm), if_pos rfl]
  norm_num

private lemma abHom_lam_toAdd (n : ℕ) (u v : Fin n) (huv : u ≠ v) :
    ((abHom n) ((lam u v huv) (a u))).toAdd v = 1 := by
  rw [lam_apply_self, MonoidHom.map_mul, toAdd_mul, Pi.add_apply, abHom_of_toAdd n v v,
    abHom_of_toAdd n u v, if_neg (fun h : v = u => huv h.symm), if_pos rfl]
  norm_num

private lemma abHom_lamNeg_toAdd (n : ℕ) (u v : Fin n) (huv : u ≠ v) :
    ((abHom n) ((lamNeg u v huv) (a u))).toAdd v = -1 := by
  rw [lamNeg_apply_self, MonoidHom.map_mul, MonoidHom.map_inv, toAdd_mul, toAdd_inv,
    Pi.add_apply, Pi.neg_apply, abHom_of_toAdd n v v, abHom_of_toAdd n u v,
    if_neg (fun h : v = u => huv h.symm), if_pos rfl]
  norm_num

private lemma abHom_sigma_toAdd (n : ℕ) (i u v : Fin n) (huv : u ≠ v) :
    ((abHom n) ((sigma i) (a u))).toAdd v = 0 := by
  by_cases hui : u = i
  · subst hui
    rw [sigma_apply_self, MonoidHom.map_inv, toAdd_inv, Pi.neg_apply, abHom_of_toAdd n u v,
      if_neg (fun h : v = u => huv h.symm)]
    norm_num
  · rw [sigma_apply_other hui, abHom_of_toAdd n u v,
      if_neg (fun h : v = u => huv h.symm)]

private lemma sAutAut_abHom_ne_zero (n : ℕ) (u v : Fin n) (huv : u ≠ v) (b e : Bool) :
    ((abHom n) ((sAutAut ⟨((u, v), (b, e)), huv⟩) (a u))).toAdd v ≠ 0 := by
  cases b <;> cases e
  · show ((abHom n) ((lamNeg u v huv) (a u))).toAdd v ≠ 0
    rw [abHom_lamNeg_toAdd n u v huv]
    norm_num
  · show ((abHom n) ((lam u v huv) (a u))).toAdd v ≠ 0
    rw [abHom_lam_toAdd n u v huv]
    norm_num
  · show ((abHom n) ((rhoNeg u v huv) (a u))).toAdd v ≠ 0
    rw [abHom_rhoNeg_toAdd n u v huv]
    norm_num
  · show ((abHom n) ((rho u v huv) (a u))).toAdd v ≠ 0
    rw [abHom_rho_toAdd n u v huv]
    norm_num

/-- A single-generator inversion `σᵢ` is **not** a Nielsen transvection (so in
particular `σᵢ ∉ SAutGen n`): `σᵢ ∈ SAutGen n` would force it to be one of the
four families `ρᵤᵥ^{±1}`, `λᵤᵥ^{±1}`, and each of those moves the generator `aᵤ`
to a reduced word of length `2` (`aᵤ·aᵥ^{±1}` or `aᵥ^{±1}·aᵤ`) while `σᵢ` has
only length-`1` or fixed values on generators. -/
theorem sigma_notMem_SAutGen (n : ℕ) (i : Fin n) : sigma i ∉ SAutGen n := by
  classical
  intro hmem
  rw [SAutGen] at hmem
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hmem
  rcases p with ⟨⟨uv, be⟩, huv⟩
  rcases uv with ⟨u, v⟩
  rcases be with ⟨b, e⟩
  have key : ((abHom n) ((sAutAut ⟨((u, v), (b, e)), huv⟩) (a u))).toAdd v
      = ((abHom n) ((sigma i) (a u))).toAdd v :=
    congrArg (fun φ : MulAut (FreeGroup (Fin n)) => ((abHom n) (φ (a u))).toAdd v) hp
  rw [abHom_sigma_toAdd n i u v huv] at key
  exact sAutAut_abHom_ne_zero n u v huv b e key

end Commons.GroupTheory.FreeGroup
