import Lie.GeneralResults
import Mathlib.Algebra.Lie.Derivation.Basic
import Lie.Tactics

section lie_semidirect

variable {K : Type*} (L J: Type*) [CommRing K] [LieRing L] [LieRing J] [LieAlgebra K L] [LieAlgebra K J]
  (φ : L →ₗ⁅K⁆ LieDerivation K J J)

/-- The semidirect product of two Lie algebras `L` and `J`, defined by specifying a homomorphism from
  `L` to the Lie algebra of derivations of `J`. -/
def LieSemidirectProduct (_ : L →ₗ⁅K⁆ LieDerivation K J J) := L × J

variable {K : Type*} {L J: Type*} [CommRing K] [LieRing L] [LieRing J] [LieAlgebra K L] [LieAlgebra K J]
  {φ : L →ₗ⁅K⁆ LieDerivation K J J}

@[inherit_doc]
notation:35 L " ⋉[" φ:35 "] " J:35 => LieSemidirectProduct L J φ

namespace LieSemidirectProduct

@[ext]
theorem ext {a b : L ⋉[φ] J} (h1 : a.1 = b.1) (h2 : a.2 = b.2) : a = b := by
  unfold LieSemidirectProduct
  ext <;> assumption

instance : AddCommGroup (LieSemidirectProduct L J φ) := (inferInstance : AddCommGroup (L × J))

instance : Module K (LieSemidirectProduct L J φ) := (inferInstance : Module K (L × J))

@[simp]
theorem add_left (a b : L ⋉[φ] J) : (a + b).1 = a.1 + b.1 := rfl

@[simp]
theorem add_right (a b : L ⋉[φ] J) : (a + b).2 = a.2 + b.2 := rfl

@[simp]
theorem zero_left : (0 : L ⋉[φ] J).1 = 0 := rfl

@[simp]
theorem zero_right : (0 : L ⋉[φ] J).2 = 0 := rfl

@[simp]
theorem neg_left (a : L ⋉[φ] J) : (-a).1 = -a.1 := rfl

@[simp]
theorem neg_right (a : L ⋉[φ] J) : (-a).2 = -a.2 := rfl

@[simp]
theorem smul_left (k : K) (a : L ⋉[φ] J) : (k • a).1 = k • a.1 := rfl

@[simp]
theorem smul_right (k : K) (a : L ⋉[φ] J) : (k • a).2 = k • a.2 := rfl

instance : Bracket (L ⋉[φ] J) (L ⋉[φ] J) := {
  bracket := fun a b ↦ ⟨⁅a.1, b.1⁆, φ a.1 b.2 - φ b.1 a.2 + ⁅a.2, b.2⁆⟩
}

lemma bracket_def (a b : L ⋉[φ] J) :
    ⁅a, b⁆ = ⟨⁅a.1, b.1⁆, φ a.1 b.2 - φ b.1 a.2 + ⁅a.2, b.2⁆⟩ := rfl

instance : LieRing (L ⋉[φ] J) := {
  (inferInstance : AddCommGroup (L ⋉[φ] J)) with
  add_lie := by
    intro x y z
    simp only [bracket_def, add_left, add_right]
    congr 1
    · simp only [add_lie]
    · simp only [LieHom.map_add, LieDerivation.coe_add, Pi.add_apply, map_add, add_lie]
      module
  lie_add := by
    intro x y z
    simp only [bracket_def, add_left, add_right]
    congr 1
    · simp only [lie_add]
    · simp only [map_add, LieHom.map_add, LieDerivation.coe_add, Pi.add_apply, lie_add]
      module
  lie_self :=by
    intro x
    simp only [bracket_def, lie_self, sub_self, add_zero]
    congr
  leibniz_lie := by
    intro x y z
    simp only [bracket_def, add_left, add_right]
    congr 1
    · simp only [lie_lie, sub_add_cancel]
    · simp only [map_add, map_sub, LieDerivation.apply_lie_eq_sub, LieHom.map_lie,
      LieDerivation.lie_apply, lie_add, lie_sub, add_lie, sub_lie, lie_lie]
      simplify_lie
}

instance : LieAlgebra K (L ⋉[φ] J) := {
  lie_smul := by
    intro k y z
    simp only [bracket_def, smul_left, lie_smul, smul_right, map_smul, LieHom.map_smul,
      LieDerivation.coe_smul, Pi.smul_apply]
    rw [Prod.smul_def]
    ext
    · simp only
    · simp only [smul_add, add_left_inj, smul_sub]
}

def inl : L →ₗ⁅K⁆ L ⋉[φ] J := {
  toFun := fun x ↦ ⟨x, 0⟩,
  map_add' := by
    intro x y
    ext
    · simp only [add_left]
    · simp only [add_right, add_zero]
  map_smul' := by
    intro k x
    ext
    · simp only [RingHom.id_apply, smul_left]
    · simp only [RingHom.id_apply, smul_right, smul_zero]
  map_lie' := by
    intro x y
    ext
    · simp only [bracket_def]
    · simp only [bracket_def, map_zero, sub_self, lie_self, add_zero]
}

def inr : J →ₗ⁅K⁆ L ⋉[φ] J := {
  toFun := fun x ↦ ⟨0, x⟩,
  map_add' := by
    intro x y
    ext
    · simp only [add_left, add_zero]
    · simp only [add_right]
  map_smul' := by
    intro k x
    ext
    · simp only [RingHom.id_apply, smul_left, smul_zero]
    · simp only [RingHom.id_apply, smul_right]
  map_lie' := by
    intro x y
    ext
    · simp only [bracket_def, lie_self, LieHom.map_zero, LieDerivation.coe_zero, Pi.zero_apply,
      sub_self, zero_add]
    · simp only [bracket_def, lie_self, LieHom.map_zero, LieDerivation.coe_zero, Pi.zero_apply,
      sub_self, zero_add]
}

def fst : L ⋉[φ] J →ₗ⁅K⁆ L := {
  toFun := fun x ↦ x.1,
  map_add' := by
    intro x y
    simp only [add_left, add_right]
  map_smul' := by
    intro k x
    simp only [smul_left, RingHom.id_apply]
  map_lie' := by
    intro x y
    simp only [bracket_def]
}

@[simp]
theorem fst_inl (x : L) : fst (inl x : L ⋉[φ] J) = x := rfl

@[simp]
theorem fst_inr (x : J) : fst (inr x : L ⋉[φ] J) = 0 := rfl

@[simp]
theorem fst_inl' (x : L) : (inl x : L ⋉[φ] J).1 = x := rfl

@[simp]
theorem fst_inr' (x : J) : (inr x : L ⋉[φ] J).1 = 0 := rfl

@[simp]
theorem snd_inl' (x : L) : (inl x : L ⋉[φ] J).2 = 0 := rfl

@[simp]
theorem snd_inr' (x : J) : (inr x : L ⋉[φ] J).2 = x := rfl

@[simp]
theorem inl_left_add_inr_right (x : L ⋉[φ] J) : inl x.1 + inr x.2 = x := by
  ext
  · simp only [add_left, fst_inl', fst_inr', add_zero]
  · simp only [add_right, snd_inl', snd_inr', zero_add]

variable (φ : L →ₗ⁅K⁆ LieDerivation K J J)

def leftSubalgebra : LieSubalgebra K (L ⋉[φ] J) := LieHom.range inl

def rightIdeal : LieIdeal K (L ⋉[φ] J) := LieHom.ker fst

def rightIdeal_equiv_right : rightIdeal φ ≃ₗ⁅K⁆ J := {
  toFun := fun x ↦ x.val.2
  map_add' := fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp only [AddMemClass.mk_add_mk, add_right]
  map_smul' := fun _ ⟨_, _⟩ ↦ by simp only [SetLike.mk_smul_mk, smul_right, RingHom.id_apply]
  map_lie' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket, bracket_def, add_eq_right]
    change x.1 = 0 at hx
    change y.1 = 0 at hy
    rw [hx, hy]
    simp only [LieHom.map_zero, LieDerivation.coe_zero, Pi.zero_apply, sub_self]
  invFun := fun x ↦ ⟨⟨0, x⟩, rfl⟩
  left_inv := by
    intro x
    have : x.val.1 = 0 := x.prop
    ext
    · rw [this]
    · rfl
  right_inv := fun _ ↦ rfl
}

theorem range_inr_eq_ker_fst : LieHom.range inr = (rightIdeal φ).toLieSubalgebra := by
  ext x
  unfold rightIdeal
  rw [← LieSubalgebra.mem_coe (LieIdeal.toLieSubalgebra K (L ⋉[φ] J) fst.ker),
    LieIdeal.coe_toLieSubalgebra, SetLike.mem_coe, LieHom.mem_ker]
  constructor
  · intro ⟨y, h⟩
    rw [← h, LieHom.coe_toLinearMap, fst_inr]
  · intro h
    use x.2
    rw [LieHom.coe_toLinearMap]
    nth_rw 2 [← inl_left_add_inr_right x]
    simp only [fst, LieHom.coe_mk] at h
    rw [h]
    simp only [LieHom.map_zero, zero_add]

theorem finrank_eq [StrongRankCondition K] [Module.Free K L] [Module.Free K J]
      [Module.Finite K L] [Module.Finite K J] :
    Module.finrank K (L ⋉[φ] J) = Module.finrank K L + Module.finrank K J :=
  Module.finrank_prod

/-- Any semidirect product of the base field with an abelian Lie algebra is almost abelian. -/
theorem isAlmostAbelian {φ : K →ₗ⁅K⁆ LieDerivation K L L} [IsLieAbelian L]
    [StrongRankCondition K] [Module.Free K L] [Module.Finite K L] :
    LieAlgebra.IsAlmostAbelian K (K ⋉[φ] L) := by
  use rightIdeal φ
  constructor
  · rw [lie_abelian_iff_equiv_lie_abelian (rightIdeal_equiv_right φ)]
    assumption
  · rw [finrank_eq, Module.finrank_self, LinearEquiv.finrank_eq (rightIdeal_equiv_right φ).toLinearEquiv, add_comm]

end LieSemidirectProduct

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- If a Lie algebra has a codimension one ideal, then is it isomorphic to a semidirect product with it. -/
theorem LieAlgebra.semidirectProduct_of_codim_one_ideal (I : LieIdeal K L)
      (hdim : Module.finrank K L = Module.finrank K I + 1) :
    ∃ φ : K →ₗ⁅K⁆ LieDerivation K I I, Nonempty (L ≃ₗ⁅K⁆ K ⋉[φ] I) := by
  --choose some element x not in I. then L is spanned by I and x.
  obtain ⟨x, hx⟩ := Submodule.compl_span_singleton_of_codim_one I.toSubmodule hdim
  --define φ as k ↦ k • ad(x) restricted to I
  let adx := ad K L x
  have adx_preserves_I : ∀ y ∈ I, adx y ∈ I := by
    intro y hy
    rw [ad_apply]
    apply lie_mem_right
    assumption
  let adxI : I →ₗ[K] I := LinearMap.restrict adx adx_preserves_I
  let adxI' : LieDerivation K I I := {
    adxI with
    leibniz' := by
      intro ⟨u, hu⟩ ⟨v, hv⟩
      simp only [LieIdeal.coe_bracket_of_module, adxI, adx]
      conv =>
        congr
        · apply LinearMap.restrict_apply
        · congr
          · rhs
            apply LinearMap.restrict_apply
          · rhs
            apply LinearMap.restrict_apply
      ext
      simp only [LieSubmodule.coe_bracket, AddSubgroupClass.coe_sub, LieAlgebra.ad_lie]
      rw [sub_eq_add_neg, lie_skew, add_comm]
  }
  let φ : K →ₗ⁅K⁆ LieDerivation K I I := {
    LinearMap.smulRight (LinearMap.id : K →ₗ[K] K) adxI' with
    map_lie' := by
      intro x y
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_smulRight,
        LinearMap.id_coe, id_eq, lie_smul, smul_lie, lie_self, smul_zero]
      simp only [Bracket.bracket]
      rw [mul_comm, sub_self, zero_smul]
  }
  use φ
  --isomorphism between K and span K {x}
  have xne0 : x ≠ 0 := by
    intro h
    rw [h, Submodule.span_zero_singleton] at hx
    have Itop := codisjoint_iff.mp hx.2
    simp only [bot_le, sup_of_le_left] at Itop
    have : Module.finrank K L = Module.finrank K I := by
      rw [← finrank_top, ← Itop]
      rfl
    linarith
  let f := LinearEquiv.toSpanSingleton K L xne0
  --construct the isomorphism
  constructor
  symm
  exact {
    toFun := fun ⟨k, v⟩ ↦ (LinearEquiv.ofComplSubmodules hx) ⟨v, LinearEquiv.toSpanSingleton K L xne0 k⟩
    map_add' := by
      intro ⟨k₁, v₁⟩ ⟨k₂, v₂⟩
      simp only [LinearEquiv.toSpanSingleton_apply, LinearEquiv.ofComplSubmodules_apply,
        LieSubmodule.coe_add]
      module
    map_smul' := by
      intro k ⟨k', v⟩
      simp only [smul_eq_mul, LinearEquiv.toSpanSingleton_apply,
        LinearEquiv.ofComplSubmodules_apply, SetLike.val_smul, RingHom.id_apply, smul_add,
        add_right_inj, mul_smul]
    map_lie' := by
      intro ⟨k₁, v₁⟩ ⟨k₂, v₂⟩
      simp only [← LieHom.coe_toLinearMap, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
        LieDerivation.coe_smul, LieDerivation.mk_coe, Pi.smul_apply, trivial_lie_zero, add_zero,
        LinearEquiv.toSpanSingleton_apply, LinearEquiv.ofComplSubmodules_apply,
        AddSubgroupClass.coe_sub, SetLike.val_smul, lie_add, add_lie, smul_lie, lie_smul, lie_self,
        smul_zero, φ, adxI', adxI, adx]
      conv =>
        lhs
        lhs
        congr
        lhs
        congr
        · rhs
          apply LinearMap.restrict_apply
        · rhs
          apply LinearMap.restrict_apply
      simp only [LieHom.coe_toLinearMap, ad_apply, SetLike.mk_smul_mk, Bracket.bracket,
        LieSubmodule.coe_add, AddSubgroupClass.coe_sub]
      simplify_lie
    invFun := fun y ↦ ⟨f.symm ((LinearEquiv.ofComplSubmodules hx).symm y).2, ((LinearEquiv.ofComplSubmodules hx).symm y).1⟩
    left_inv := by
      intro ⟨k, v⟩
      simp only [LinearEquiv.toSpanSingleton_apply, LinearEquiv.ofComplSubmodules_apply, map_add,
        Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.fst_add, Prod.smul_fst,
        LinearEquiv.ofComplSubmodules_symm_apply_left hx v.val v.prop,
        LinearEquiv.ofComplSubmodules_symm_apply_right hx (k • x) (by rw [Submodule.mem_span_singleton]; use k)]
      ext
      · simp only [map_zero, zero_add]
        rw [LinearEquiv.toSpanSingleton_symm_apply]
      · simp only [Subtype.coe_eta, add_zero]
    right_inv := by
      intro y
      simp only [LinearEquiv.toSpanSingleton_apply, LinearEquiv.ofComplSubmodules_apply]
      rw [LinearEquiv.toSpanSingleton_symm_apply']
      exact (LinearEquiv.ofComplSubmodules_symm_add hx y).symm
  }


end lie_semidirect

section lie_direct

/- Direct product/sum of Lie algebra -/

variable {K L J : Type*} [CommRing K] [LieRing L] [LieRing J] [LieAlgebra K L] [LieAlgebra K J]

instance : Bracket (L × J) (L × J) := {
  bracket := fun a b ↦ ⟨⁅a.1, b.1⁆, ⁅a.2, b.2⁆⟩
}

lemma Prod.bracket_def (a b : L × J) :
    ⁅a, b⁆ = ⟨⁅a.1, b.1⁆, ⁅a.2, b.2⁆⟩ := rfl

instance : LieRing (L × J) := {
  (inferInstance : AddCommGroup (L × J)) with
  add_lie := fun _ _ _ ↦ by simp only [Prod.bracket_def, Prod.fst_add, add_lie, Prod.snd_add, Prod.mk_add_mk]
  lie_add := fun _ _ ↦ by simp only [Prod.bracket_def, Prod.fst_add, lie_add, Prod.snd_add, Prod.mk_add_mk, implies_true]
  lie_self := fun _ ↦ by simp only [Prod.bracket_def, lie_self, Prod.mk_zero_zero]
  leibniz_lie := fun _ _ _ ↦ by simp only [Prod.bracket_def, lie_lie, Prod.mk_add_mk, sub_add_cancel]
}

instance : LieAlgebra K (L × J) := {
  lie_smul := fun _ _ _ ↦ by simp only [Prod.bracket_def, Prod.smul_fst, lie_smul, Prod.smul_snd, Prod.smul_mk]
}

variable (K L J : Type*) [CommRing K] [LieRing L] [LieRing J] [LieAlgebra K L] [LieAlgebra K J]

def LieHom.inl : L →ₗ⁅K⁆ L × J := {
  toFun := fun x ↦ ⟨x, 0⟩,
  map_add' := by
    intro x y
    ext <;> simp only [Prod.mk_add_mk, add_zero]
  map_smul' := by
    intro k x
    ext <;> simp only [RingHom.id_apply, Prod.smul_mk, smul_zero]
  map_lie' := by
    intro x y
    ext <;> simp only [Prod.bracket_def, lie_self]
}

def LieHom.inr : J →ₗ⁅K⁆ L × J := {
  toFun := fun x ↦ ⟨0, x⟩,
  map_add' := by
    intro x y
    ext <;> simp only [Prod.mk_add_mk, add_zero]
  map_smul' := by
    intro k x
    ext <;> simp only [RingHom.id_apply, Prod.smul_mk, smul_zero]
  map_lie' := by
    intro x y
    ext <;> simp only [Prod.bracket_def, lie_self]
}

def LieHom.fst : L × J →ₗ⁅K⁆ L := {
  toFun := fun x ↦ x.1,
  map_add' := by
    intro x y
    simp only [Prod.fst_add]
  map_smul' := by
    intro k x
    simp only [Prod.smul_fst, RingHom.id_apply]
  map_lie' := rfl
}

def LieHom.snd : L × J →ₗ⁅K⁆ J := {
  toFun := fun x ↦ x.2,
  map_add' := by
    intro x y
    simp only [Prod.snd_add]
  map_smul' := by
    intro k x
    simp only [Prod.smul_snd, RingHom.id_apply]
  map_lie' := rfl
}

def leftIdeal : LieIdeal K (L × J) := LieHom.ker (LieHom.snd K L J)

def leftIdeal_equiv_left : leftIdeal K L J ≃ₗ⁅K⁆ L := {
  toFun := fun x ↦ x.val.1
  map_add' := fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp only [AddMemClass.mk_add_mk, Prod.fst_add]
  map_smul' := fun _ ⟨_, _⟩ ↦ by simp only [SetLike.mk_smul_mk, Prod.smul_fst,
    RingHom.id_apply]
  map_lie' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket, Prod.bracket_def, add_eq_right]
  invFun := fun x ↦ ⟨⟨x, 0⟩, rfl⟩
  left_inv := by
    intro x
    have : x.val.2 = 0 := x.prop
    ext
    · rfl
    · rw [this]
  right_inv := fun _ ↦ rfl
}

def rightIdeal : LieIdeal K (L × J) := LieHom.ker (LieHom.fst K L J)

def rightIdeal_equiv_right : rightIdeal K L J ≃ₗ⁅K⁆ J := {
  toFun := fun x ↦ x.val.2
  map_add' := fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp only [AddMemClass.mk_add_mk, Prod.snd_add]
  map_smul' := fun _ ⟨_, _⟩ ↦ by simp only [SetLike.mk_smul_mk, Prod.smul_snd,
    RingHom.id_apply]
  map_lie' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket, Prod.bracket_def, add_eq_right]
  invFun := fun x ↦ ⟨⟨0, x⟩, rfl⟩
  left_inv := by
    intro x
    have : x.val.1 = 0 := x.prop
    ext
    · rw [this]
    · rfl
  right_inv := fun _ ↦ rfl
}

def Prod.toLieSemidirectProduct : (L × J) ≃ₗ⁅K⁆ L ⋉[(0 : L →ₗ⁅K⁆ LieDerivation K J J)] J := {
  LinearEquiv.refl K (L × J) with
  map_lie' := by
    simp only [LinearEquiv.refl_toLinearMap, bracket_def, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, LinearMap.id_coe, id_eq, LieSemidirectProduct.bracket_def,
      LieHom.coe_zero, Pi.zero_apply, LieDerivation.coe_zero, sub_self, zero_add, implies_true]
}

end lie_direct
